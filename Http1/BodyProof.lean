import Http1.Body

/-!
# The byte boundary is exact

`no_desync` proves the framing *decision* is unambiguous. Here we prove the layer below: once the
decision is made, the point where the body ends is a determined function of the bytes.
`takeExact_append` (Body.lean) does the length case; this file does the chunked case, ending in
`readChunked_writeChunked`: a chunked body written from non-empty payloads, followed by any continuation,
reads back as exactly those payloads and exactly that continuation.
-/

namespace Http1


def hexFoldl (acc : Nat) : List UInt8 → Nat
  | [] => acc
  | b :: bs => hexFoldl (acc * 16 + (hexVal b).getD 0) bs

def allHex (xs : List UInt8) : Prop := ∀ b ∈ xs, (hexVal b).isSome

theorem hexFoldl_append (acc : Nat) (xs ys : List UInt8) :
    hexFoldl acc (xs ++ ys) = hexFoldl (hexFoldl acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a as ih => simp [hexFoldl, ih]

theorem hexVal_hexDigit : ∀ (d : Nat), d < 16 → hexVal (hexDigit d) = some d
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | 13, _ => by decide
  | 14, _ => by decide
  | 15, _ => by decide
  | (n+16), h => by omega

theorem toHexGo_inv (fuel m : Nat) (h : m < 16 ^ fuel) : hexFoldl 0 (toHexGo fuel m) = m := by
  induction fuel generalizing m with
  | zero => simp at h; simp [h, toHexGo, hexFoldl]
  | succ f ih =>
    match m with
    | 0 => simp [toHexGo, hexFoldl]
    | k + 1 =>
      rw [show toHexGo (f+1) (k+1) = toHexGo f ((k+1)/16) ++ [hexDigit ((k+1)%16)] from rfl]
      rw [hexFoldl_append]
      have hdiv : (k+1)/16 < 16 ^ f := by rw [Nat.pow_succ] at h; omega
      rw [ih _ hdiv]
      simp only [hexFoldl, hexVal_hexDigit ((k+1)%16) (by omega)]
      simp; omega

-- hexVal of the two line-ending bytes is none, so a hex-digit list contains neither.
theorem hexVal_13 : hexVal 13 = none := by decide
theorem hexVal_10 : hexVal 10 = none := by decide

theorem allHex_not_mem_13 {xs : List UInt8} (h : allHex xs) : (13:UInt8) ∉ xs := by
  intro hm; have := h 13 hm; rw [hexVal_13] at this; simp at this

-- Every byte toHexGo emits is some hexDigit d with d < 16.
theorem mem_toHexGo {fuel m b} (h : b ∈ toHexGo fuel m) : ∃ d, d < 16 ∧ b = hexDigit d := by
  induction fuel generalizing m with
  | zero => simp [toHexGo] at h
  | succ f ih =>
    match m with
    | 0 => simp [toHexGo] at h
    | k+1 =>
      rw [show toHexGo (f+1) (k+1) = toHexGo f ((k+1)/16) ++ [hexDigit ((k+1)%16)] from rfl] at h
      rcases List.mem_append.mp h with h1 | h1
      · exact ih h1
      · simp at h1; exact ⟨(k+1)%16, by omega, h1⟩

theorem allHex_toHex (n : Nat) : allHex (toHex n) := by
  unfold toHex
  by_cases hn : n = 0
  · subst hn; intro b hb; simp at hb; subst hb; rw [hexVal_hexDigit 0 (by omega)]; simp
  · rw [if_neg hn]; intro b hb
    obtain ⟨d, hd, rfl⟩ := mem_toHexGo hb; rw [hexVal_hexDigit d hd]; simp

theorem toHex_ne_nil (n : Nat) : toHex n ≠ [] := by
  unfold toHex
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn]
    match n, hn with
    | k+1, _ => rw [show toHexGo (k+1+1) (k+1) = toHexGo (k+1) ((k+1)/16) ++ [hexDigit ((k+1)%16)] from rfl]; simp

theorem hexFoldl_toHex (n : Nat) : hexFoldl 0 (toHex n) = n := by
  unfold toHex
  by_cases hn : n = 0
  · subst hn; simp [hexFoldl, hexVal_hexDigit 0 (by omega)]
  · rw [if_neg hn]; refine toHexGo_inv (n+1) n ?_
    calc n < 2^n := Nat.lt_two_pow_self
      _ ≤ 16^n := Nat.pow_le_pow_left (by omega) n
      _ ≤ 16^(n+1) := Nat.pow_le_pow_right (by omega) (by omega)

-- Step A (from /tmp/hex.lean), the hex-list reader.
theorem readChunkSizeF_hexList (xs : List UInt8) (hx : allHex xs) (h13 : (13:UInt8) ∉ xs) :
    ∀ (fuel acc : Nat) (seen : Bool) (tail : List UInt8),
      xs.length < fuel → (seen = true ∨ xs ≠ []) →
      readChunkSizeF fuel acc seen (xs ++ 13 :: 10 :: tail) = some (hexFoldl acc xs, tail) := by
  induction xs with
  | nil =>
    intro fuel acc seen tail _ hseen
    rcases hseen with h | h
    · cases fuel with
      | zero => simp at *
      | succ f => simp [readChunkSizeF, hexFoldl, h]
    · exact absurd rfl h
  | cons a as ih =>
    intro fuel acc seen tail hfuel _
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      have ha : (hexVal a).isSome := hx a (by simp)
      have hane13 : (a == 13) = false := by
        have : a ≠ 13 := fun h => h13 (by simp [h]); simp [this]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ha
      have hstep : readChunkSizeF (f+1) acc seen ((a :: as) ++ 13 :: 10 :: tail)
                 = readChunkSizeF f (acc * 16 + v) true (as ++ 13 :: 10 :: tail) := by
        simp [List.cons_append, readChunkSizeF, hane13, hv]
      rw [hstep]
      have hxas : allHex as := fun b hb => hx b (by simp [hb])
      have h13as : (13:UInt8) ∉ as := fun h => h13 (by simp [h])
      have := ih hxas h13as f (acc * 16 + v) true tail (by simp at hfuel ⊢; omega) (Or.inl rfl)
      rw [this]; simp [hexFoldl, hv]

-- The size round-trip: a canonical hex size then CRLF reads back exactly.
theorem readChunkSize_toHex (n : Nat) (tail : List UInt8) :
    readChunkSize (toHex n ++ 13 :: 10 :: tail) = some (n, tail) := by
  unfold readChunkSize
  have hx := allHex_toHex n
  have h13 := allHex_not_mem_13 hx
  have hne := toHex_ne_nil n
  rw [readChunkSizeF_hexList (toHex n) hx h13 _ 0 false tail (by simp only [List.length_append, List.length_cons]; omega) (Or.inr hne)]
  rw [hexFoldl_toHex]


theorem readChunked_gen (chunks : List (List UInt8)) (hne : ∀ c ∈ chunks, c ≠ []) :
    ∀ (acc rest : List UInt8) (fuel : Nat), chunks.length < fuel →
      readChunkedF fuel acc ((chunks.flatMap writeChunk) ++ (toHex 0 ++ CRLF ++ CRLF) ++ rest)
        = some (acc ++ chunks.flatMap id, rest) := by
  induction chunks with
  | nil =>
    intro acc rest fuel hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      rw [readChunkedF]
      simp only [List.flatMap_nil, List.nil_append, CRLF, List.append_assoc, List.cons_append,
        readChunkSize_toHex]
      simp
  | cons c cs ih =>
    intro acc rest fuel hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      have hc : c ≠ [] := hne c (by simp)
      have hcpos : c.length ≠ 0 := fun h => hc (List.length_eq_zero_iff.mp h)
      obtain ⟨k, hk⟩ : ∃ k, c.length = k + 1 := ⟨c.length - 1, by omega⟩
      rw [readChunkedF]
      simp only [List.flatMap_cons, writeChunk, CRLF, List.append_assoc, List.cons_append,
        List.nil_append, readChunkSize_toHex, hk]
      rw [← hk]
      generalize hT : List.flatMap writeChunk cs ++ (toHex 0 ++ 13 :: 10 :: 13 :: 10 :: rest) = TAIL
      rw [if_pos (by simp), show (c ++ 13 :: 10 :: TAIL).drop c.length = 13 :: 10 :: TAIL from by simp,
          show (c ++ 13 :: 10 :: TAIL).take c.length = c from by simp]
      have ihc := ih (fun d hd => hne d (by simp [hd])) (acc ++ c) rest f (by simp at hfuel ⊢; omega)
      show readChunkedF f (acc ++ c) TAIL = _
      rw [← hT]
      simp only [CRLF, List.cons_append, List.nil_append, List.append_assoc] at ihc
      rw [ihc]
      simp [List.flatMap_cons, List.append_assoc]

theorem length_le_writeChunked (chunks : List (List UInt8)) :
    chunks.length ≤ (chunks.flatMap writeChunk).length := by
  induction chunks with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (writeChunk c).length := by unfold writeChunk CRLF; simp; omega
    omega

/-- **The chunked boundary is exact.** A chunked body written from non-empty payloads, followed by any
continuation `rest`, reads back as exactly the concatenated payloads, leaving exactly `rest`. So where a
chunked message ends — at the `0 CRLF CRLF` terminator — is a determined function of the bytes. -/
theorem readChunked_writeChunked (chunks : List (List UInt8)) (hne : ∀ c ∈ chunks, c ≠ [])
    (rest : List UInt8) :
    readChunked (writeChunked chunks ++ rest) = some (chunks.flatMap id, rest) := by
  unfold readChunked writeChunked
  have h := readChunked_gen chunks hne [] rest ((writeChunked chunks ++ rest).length + 1)
    (by unfold writeChunked; simp only [List.length_append]; have := length_le_writeChunked chunks; omega)
  simpa [writeChunked, List.append_assoc] using h

end Http1
