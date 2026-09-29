-- Prove2me | solution 1 for mme_dwz_fourth_exact_retained_entropy_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T07:25:44.518612+00:00
-- url     : https://prove2.me/submissions/38c96a46-ed30-4ede-9e98-1c0f7f2efcd1

import Definitions.Def_mme_dwz_fourth_exact_retained_entropy_arithmetic_data

open MME.DWZFourthRetainedEntropy MME.DWZFourthLogScaleTable

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
-- check the chunks one after another, so each chunk's kernel caches are freed before the next
set_option Elab.async false

namespace MME.DWZFourthRetainedEntropy.Fast


/-- A fixed plan of binary splits of an index range. -/
inductive Plan where
  | leaf
  | split (n : Nat) (p q : Plan)

/-- `l[i]?` following the plan: at each split keep only the half containing `i`.  The kernel
caches every `take`/`drop` sublist the first time it builds one, so after warm-up a lookup costs
the plan's depth plus a short leaf, instead of `i` list steps. -/
def look {α : Type} : Plan → List α → Nat → Option α
  | .leaf, l, i => l[i]?
  | .split n p q, l, i => if i < n then look p (l.take n) i else look q (l.drop n) (i - n)

theorem look_eq {α : Type} (p : Plan) (l : List α) (i : Nat) : look p l i = l[i]? := by
  induction p generalizing l i with
  | leaf => rfl
  | split n p q ihp ihq =>
    simp only [look]
    split
    · rw [ihp, List.getElem?_take_of_lt ‹_›]
    · rw [ihq, List.getElem?_drop]
      congr 1
      omega

/-- The log table as one list, appended to the *right*: `entries` nests its 31 appends to the
left, so the kernel would walk each early entry through up to 30 appends. -/
def flatEntries : List (Rat × Nat) :=
  chunk0.toList ++ (chunk1.toList ++ (chunk2.toList ++ (chunk3.toList ++ (chunk4.toList ++ (chunk5.toList ++ (chunk6.toList ++ (chunk7.toList ++ (chunk8.toList ++ (chunk9.toList ++ (chunk10.toList ++ (chunk11.toList ++ (chunk12.toList ++ (chunk13.toList ++ (chunk14.toList ++ (chunk15.toList ++ (chunk16.toList ++ (chunk17.toList ++ (chunk18.toList ++ (chunk19.toList ++ (chunk20.toList ++ (chunk21.toList ++ (chunk22.toList ++ (chunk23.toList ++ (chunk24.toList ++ (chunk25.toList ++ (chunk26.toList ++ (chunk27.toList ++ (chunk28.toList ++ (chunk29.toList ++ chunk30.toList)))))))))))))))))))))))))))))

theorem entries_toList : entries.toList = flatEntries := by
  simp only [entries, Array.toList_append, List.append_assoc, flatEntries]

def planE : Plan := (.split 973 (.split 486 (.split 243 (.split 121 (.split 60 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))) (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))))) (.split 121 (.split 60 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))) (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))))) (.split 243 (.split 121 (.split 60 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))) (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))))) (.split 122 (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))) (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))))))) (.split 487 (.split 243 (.split 121 (.split 60 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))) (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))))) (.split 122 (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))) (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))))) (.split 243 (.split 121 (.split 60 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))) (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))))) (.split 122 (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf)))) (.split 61 (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))) (.split 30 (.split 15 (.split 7 .leaf .leaf) (.split 7 .leaf .leaf)) (.split 15 (.split 7 .leaf .leaf) (.split 8 .leaf .leaf))))))))
def planR : Plan := (.split 794 (.split 397 (.split 198 (.split 99 (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))) (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))))) (.split 99 (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))) (.split 50 (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))))) (.split 198 (.split 99 (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))) (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))))) (.split 99 (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))) (.split 50 (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))))))) (.split 397 (.split 198 (.split 99 (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))) (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))))) (.split 99 (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))) (.split 50 (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))))) (.split 199 (.split 99 (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))) (.split 50 (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))))) (.split 99 (.split 49 (.split 24 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)))) (.split 50 (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))) (.split 25 (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf)) (.split 12 (.split 6 .leaf .leaf) (.split 6 .leaf .leaf))))))))

def tableAt (i : Nat) : Option (Rat × Nat) := look planE flatEntries i
def recordAt (i : Nat) : Option EntropyRecord := look planR entropyRecords.toList i

theorem entries_get (i : Nat) : entries[i]? = tableAt i := by
  rw [tableAt, look_eq, ← entries_toList, Array.getElem?_toList]

theorem records_get (i : Nat) : entropyRecords[i]? = recordAt i := by
  rw [recordAt, look_eq, Array.getElem?_toList]

/-- `entropyEndpoint` with the table lookup as a parameter. -/
def endpointWith (tbl : Nat → Option (Rat × Nat)) (useUpper : Bool) : List Nat → Option Rat
  | [] => some 0
  | logIndex :: tail => do
      let entry <- tbl logIndex
      let rest <- endpointWith tbl useUpper tail
      let logBound := if useUpper then
        MME.autoScaledLogLower entry.1 entry.2 6
      else
        MME.autoScaledLogUpper entry.1 entry.2 6
      pure (-(entry.1 * logBound) + rest)

theorem endpoint_eq (useUpper : Bool) (cells : List Nat) :
    entropyEndpoint useUpper cells = endpointWith tableAt useUpper cells := by
  induction cells with
  | nil => rfl
  | cons x t ih => simp only [entropyEndpoint, endpointWith, ih, entries_get]

def recordAccepts' (record : EntropyRecord) : Bool :=
  match endpointWith tableAt false record.cells, endpointWith tableAt true record.cells with
  | some lower, some upper =>
      decide (record.lowerFloor <= lower /\ upper <= record.upperCeiling)
  | _, _ => false

theorem recordAccepts_eq : recordAccepts = recordAccepts' := by
  funext r
  simp only [recordAccepts, recordAccepts', endpoint_eq]
  rfl

def termValue' (term : EntropyTerm) : Option Rat := do
  let record <- recordAt term.recordIndex
  let endpoint := if term.useUpper then record.upperCeiling
    else record.lowerFloor
  pure (term.coefficient * endpoint)

theorem termValue_eq : termValue = termValue' := by
  funext t
  simp only [termValue, termValue', records_get]

def termsValue' : List EntropyTerm -> Option Rat
  | [] => some 0
  | term :: tail => do
      let value <- termValue' term
      let rest <- termsValue' tail
      pure (value + rest)

theorem termsValue_eq (ts : List EntropyTerm) : termsValue ts = termsValue' ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [termsValue, termsValue', termValue_eq, ih]

def branchAccepts' (branch : FloorBranch) : Bool :=
  branch.terms.all termSafe &&
    match termsValue' branch.terms with
    | none => false
    | some value =>
        decide (branch.retainedFloor <= branch.constant + value)

theorem branchAccepts_eq : branchAccepts = branchAccepts' := by
  funext b
  simp only [branchAccepts, branchAccepts', termsValue_eq]
  rfl

theorem check_eq : checkRetainedEntropy =
    (entropyRecords.toList.all recordAccepts' && obligations.toList.all branchAccepts') := by
  simp only [checkRetainedEntropy, recordAccepts_eq, branchAccepts_eq, Array.all_toList]


theorem all_of_take_drop {α : Type} (p : α → Bool) (l : List α) (n : Nat)
    (h1 : (l.take n).all p = true) (h2 : (l.drop n).all p = true) : l.all p = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2]
  rfl

/-! The records half, in 8 kernel checks of 200 records each (one check of all 1589
peaks near 5 GB; the verifier's container has 3 GB). -/
theorem records0 : (entropyRecords.toList.take 200).all recordAccepts' = true := by decide +kernel
theorem records1 : ((entropyRecords.toList.drop 200).take 200).all recordAccepts' = true := by decide +kernel
theorem records2 : (((entropyRecords.toList.drop 200).drop 200).take 200).all recordAccepts' = true := by decide +kernel
theorem records3 : ((((entropyRecords.toList.drop 200).drop 200).drop 200).take 200).all recordAccepts' = true := by decide +kernel
theorem records4 : (((((entropyRecords.toList.drop 200).drop 200).drop 200).drop 200).take 200).all recordAccepts' = true := by decide +kernel
theorem records5 : ((((((entropyRecords.toList.drop 200).drop 200).drop 200).drop 200).drop 200).take 200).all recordAccepts' = true := by decide +kernel
theorem records6 : (((((((entropyRecords.toList.drop 200).drop 200).drop 200).drop 200).drop 200).drop 200).take 200).all recordAccepts' = true := by decide +kernel
theorem records7 : (((((((entropyRecords.toList.drop 200).drop 200).drop 200).drop 200).drop 200).drop 200).drop 200).all recordAccepts' = true := by decide +kernel

theorem obligationsOk : obligations.toList.all branchAccepts' = true := by decide +kernel

theorem recordsOk : entropyRecords.toList.all recordAccepts' = true :=
  all_of_take_drop _ _ 200 records0 <|
    all_of_take_drop _ _ 200 records1 <|
    all_of_take_drop _ _ 200 records2 <|
    all_of_take_drop _ _ 200 records3 <|
    all_of_take_drop _ _ 200 records4 <|
    all_of_take_drop _ _ 200 records5 <|
    all_of_take_drop _ _ 200 records6 records7

end MME.DWZFourthRetainedEntropy.Fast

open MME.DWZFourthRetainedEntropy.Fast in
theorem solution : checkRetainedEntropy = true := by
  rw [check_eq, recordsOk, obligationsOk]
  rfl
