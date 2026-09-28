import Http1.Body

/-!
# The header-block boundary is unique

The body-boundary proofs (`Body.lean`, `BodyProof.lean`) assume you already know where the header block
ends and the body begins. This file proves *that* split is itself determined by the bytes: a canonical
header block — lines each ended by CRLF, closed by a blank line — followed by any continuation is read back
as exactly those lines, leaving exactly the continuation.

Two things fall out. A line is terminated only by CRLF, so a header line ended by a bare LF is not
recognised (the reader rejects, rather than guessing a boundary — the choice that keeps it in step with a
CRLF-framing peer). And the blank line closes the block at a determined point, so the body starts at one
determined offset.
-/

namespace Http1

/-- Read one line: the bytes up to the first CRLF, and the remainder after it. `fuel` bounds the length. -/
def readLineF : Nat → List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, _, _ => none
  | fuel + 1, acc, input =>
    match input with
    | [] => none
    | b :: rest =>
      if b == 13 then
        match rest with
        | 10 :: rest2 => some (acc.reverse, rest2)
        | _ => none
      else readLineF fuel (b :: acc) rest

def readLine (bs : List UInt8) : Option (List UInt8 × List UInt8) := readLineF (bs.length + 1) [] bs

/-- Read a header block: lines until a blank line, returning the lines and the remainder after the blank
line. A blank line (an immediate CRLF) closes the block. `fuel` bounds the number of lines. -/
def readBlockF : Nat → List (List UInt8) → List UInt8 → Option (List (List UInt8) × List UInt8)
  | 0, _, _ => none
  | fuel + 1, acc, input =>
    match readLine input with
    | none => none
    | some ([], rest) => some (acc.reverse, rest)        -- an empty line is the blank line: end of block
    | some (line, rest) => readBlockF fuel (line :: acc) rest

def readBlock (bs : List UInt8) : Option (List (List UInt8) × List UInt8) :=
  readBlockF (bs.length + 1) [] bs

/-- Serialize one line: its bytes then CRLF. -/
def serLine (l : List UInt8) : List UInt8 := l ++ CRLF

/-- Serialize a header block: each line, then a closing blank line. -/
def serBlock (lines : List (List UInt8)) : List UInt8 := (lines.flatMap serLine) ++ CRLF

/-! ## Reading a line inverts writing it -/

/-- A CR-free line followed by CRLF and any remainder reads back as exactly the line and the remainder. The
`13 ∉ l` hypothesis is what rules out a bare LF or an embedded CRLF creating a second boundary. -/
theorem readLineF_serLine (l : List UInt8) (h13 : (13:UInt8) ∉ l) :
    ∀ (fuel : Nat) (acc rest : List UInt8), l.length < fuel →
      readLineF fuel acc (l ++ 13 :: 10 :: rest) = some (acc.reverse ++ l, rest) := by
  induction l with
  | nil =>
    intro fuel acc rest _
    cases fuel with
    | zero => simp at *
    | succ f => simp [readLineF]
  | cons a as ih =>
    intro fuel acc rest hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      have hane : (a == 13) = false := by
        have : a ≠ 13 := fun h => h13 (by simp [h]); simp [this]
      have h13as : (13:UInt8) ∉ as := fun h => h13 (by simp [h])
      simp only [List.cons_append, readLineF, hane]
      rw [ih h13as f (a :: acc) rest (by simp at hfuel ⊢; omega)]
      simp

theorem readLine_serLine (l rest : List UInt8) (h13 : (13:UInt8) ∉ l) :
    readLine (l ++ 13 :: 10 :: rest) = some (l, rest) := by
  unfold readLine
  rw [readLineF_serLine l h13 _ [] rest (by simp only [List.length_append, List.length_cons]; omega)]
  simp

/-! ## Reading a block inverts writing it -/

/-- **The header-block boundary is unique.** A block of non-empty, CR-free lines, closed by a blank line and
followed by any continuation `rest`, reads back as exactly those lines, leaving exactly `rest`. So where the
headers end and the body begins is a determined function of the bytes. -/
theorem readBlockF_serBlock (lines : List (List UInt8))
    (hne : ∀ l ∈ lines, l ≠ []) (h13 : ∀ l ∈ lines, (13:UInt8) ∉ l) :
    ∀ (acc : List (List UInt8)) (rest : List UInt8) (fuel : Nat), lines.length < fuel →
      readBlockF fuel acc ((lines.flatMap serLine) ++ CRLF ++ rest)
        = some (acc.reverse ++ lines, rest) := by
  induction lines with
  | nil =>
    intro acc rest fuel hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.flatMap_nil, List.nil_append, CRLF, readBlockF]
      rw [show ([13,10] ++ rest) = [] ++ 13 :: 10 :: rest by simp]
      rw [readLine_serLine [] rest (by simp)]
      simp
  | cons l ls ih =>
    intro acc rest fuel hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      have hl : l ≠ [] := hne l (by simp)
      have hl13 : (13:UInt8) ∉ l := h13 l (by simp)
      obtain ⟨a, as, rfl⟩ : ∃ a as, l = a :: as := by
        cases l with
        | nil => exact absurd rfl hl
        | cons a as => exact ⟨a, as, rfl⟩
      rw [readBlockF]
      simp only [List.flatMap_cons, serLine, CRLF, List.append_assoc, List.cons_append, List.nil_append]
      have hrl : readLine (a :: (as ++ 13 :: 10 :: (List.flatMap serLine ls ++ 13 :: 10 :: rest)))
               = some (a :: as, List.flatMap serLine ls ++ 13 :: 10 :: rest) := by
        rw [show a :: (as ++ 13 :: 10 :: (List.flatMap serLine ls ++ 13 :: 10 :: rest))
              = (a :: as) ++ 13 :: 10 :: (List.flatMap serLine ls ++ 13 :: 10 :: rest) from rfl]
        exact readLine_serLine (a :: as) _ hl13
      rw [hrl]
      show readBlockF f ((a :: as) :: acc) (List.flatMap serLine ls ++ 13 :: 10 :: rest) = _
      have ihc := ih (fun x hx => hne x (by simp [hx])) (fun x hx => h13 x (by simp [hx]))
        ((a :: as) :: acc) rest f (by simp at hfuel ⊢; omega)
      simp only [CRLF, List.cons_append, List.nil_append, List.append_assoc] at ihc
      rw [ihc]
      simp

theorem length_le_serBlock (lines : List (List UInt8)) :
    lines.length ≤ (lines.flatMap serLine).length := by
  induction lines with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (serLine c).length := by unfold serLine CRLF; simp
    omega

/-- The public statement: `readBlock` recovers a serialized header block and the exact remainder. -/
theorem readBlock_serBlock (lines : List (List UInt8))
    (hne : ∀ l ∈ lines, l ≠ []) (h13 : ∀ l ∈ lines, (13:UInt8) ∉ l) (rest : List UInt8) :
    readBlock (serBlock lines ++ rest) = some (lines, rest) := by
  unfold readBlock serBlock
  have h := readBlockF_serBlock lines hne h13 [] rest ((serBlock lines ++ rest).length + 1)
    (by unfold serBlock; simp only [List.length_append]
        have := length_le_serBlock lines; omega)
  simpa [serBlock, List.append_assoc] using h

end Http1
