import Http1.Header

/-!
# Header fields have one reading

`readBlock` recovers the header *lines* uniquely. This file goes one level finer: a line is split into a
field (name and value) at the first colon, and that split is unique too. `parseField_serField` proves the
reader inverts the writer on canonical fields, so a header block determines not just its lines but its list
of `(name, value)` fields — the input to the framing decision `frame`.

The split is at the *first* colon, the name keeps no trailing whitespace, and the value is OWS-trimmed —
the points where lenient parsers disagree (a space before the colon, a second colon) are pinned down.
-/

namespace Http1

def spByte : UInt8 := 32
def tabByte : UInt8 := 9

/-- Split a line at the first colon: the name (before it) and the value bytes (after it). `none` if there is
no colon. Structural on the list. -/
def splitColon : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest => if b == 58 then some ([], rest) else (splitColon rest).map (fun (n, v) => (b :: n, v))

/-- Parse a header line into a field: name up to the first colon (non-empty, not ending in whitespace), and
the OWS-trimmed value. Rejects a line with no colon, an empty name, or whitespace before the colon. -/
def parseField (line : List UInt8) : Option Field :=
  match splitColon line with
  | none => none
  | some (name, afterColon) =>
    if name == [] || name.getLast? == some spByte || name.getLast? == some tabByte then none
    else some ⟨name, trimOWS afterColon⟩

/-- Serialize a field canonically: `name ": " value`. -/
def serField (f : Field) : List UInt8 := f.name ++ [58, spByte] ++ f.value

/-- What a field must look like to round-trip: a non-empty, colon-free name that does not end in whitespace,
and a value already free of leading and trailing whitespace. These are exactly the canonical-form rules. -/
structure Canonical (f : Field) : Prop where
  name_ne : f.name ≠ []
  name_no_colon : (58:UInt8) ∉ f.name
  name_no_trail_sp : f.name.getLast? ≠ some spByte
  name_no_trail_tab : f.name.getLast? ≠ some tabByte
  value_trimmed : trimOWS f.value = f.value

theorem splitColon_append (name rest : List UInt8) (h : (58:UInt8) ∉ name) :
    splitColon (name ++ 58 :: rest) = some (name, rest) := by
  induction name with
  | nil => simp [splitColon]
  | cons a as ih =>
    have hane : (a == 58) = false := by
      have : a ≠ 58 := fun h' => h (by simp [h']); simp [this]
    have has : (58:UInt8) ∉ as := fun h' => h (by simp [h'])
    simp [splitColon, hane, ih has]

/-- The value written after `": "` trims back to the original value: dropping the one prepended space
reduces to trimming the already-trimmed value. -/
theorem trimOWS_sp_cons (v : List UInt8) (hv : trimOWS v = v) : trimOWS (spByte :: v) = v := by
  have hdrop : (spByte :: v).dropWhile cOWS = v.dropWhile cOWS := by
    simp [List.dropWhile, cOWS, spByte]
  unfold trimOWS at hv ⊢
  rw [hdrop]; exact hv

/-- **A header field has one reading.** A canonical field serialized as `name ": " value` parses back to
exactly that field. -/
theorem parseField_serField (f : Field) (hc : Canonical f) : parseField (serField f) = some f := by
  unfold parseField serField
  rw [show f.name ++ [58, spByte] ++ f.value = f.name ++ 58 :: spByte :: f.value by simp]
  rw [splitColon_append f.name (spByte :: f.value) hc.name_no_colon]
  have hcond : (f.name == [] || f.name.getLast? == some spByte || f.name.getLast? == some tabByte) = false := by
    have h1 : (f.name == []) = false := by simp [hc.name_ne]
    have h2 : (f.name.getLast? == some spByte) = false := by simp [hc.name_no_trail_sp]
    have h3 : (f.name.getLast? == some tabByte) = false := by simp [hc.name_no_trail_tab]
    simp [h1, h2, h3]
  simp only [hcond, Bool.false_eq_true, if_false, trimOWS_sp_cons f.value hc.value_trimmed]

/-- A list of canonical fields serialized and re-parsed recovers the same list. -/
theorem mapM_parseField_serField (fields : List Field) (hc : ∀ f ∈ fields, Canonical f) :
    (fields.map serField).mapM parseField = some fields := by
  induction fields with
  | nil => rfl
  | cons f fs ih =>
    have hf := parseField_serField f (hc f (by simp))
    have hfs := ih (fun g hg => hc g (by simp [hg]))
    simp [List.map_cons, List.mapM_cons, hf, hfs]

end Http1
