-- Prove2me | solution 1 for RelWalkCount.head_q_of_mem_walks
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T15:17:36.437254+00:00
-- url     : https://prove2.me/submissions/95e9f7fd-a594-4752-a61e-70907f415d2f

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
open RelWalkCount Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ι → Prop) [DecidableRel r] :
    ∀ (n : ℕ) (a b : ι) (l : List ι), l ∈ walks r n a b → l.head? = some a := by
  intro n a b l hl
  cases n with
  | zero =>
    -- the only walk of length `0` is `[a]`
    simp only [walks] at hl
    split_ifs at hl with hab
    · rw [Finset.mem_singleton] at hl
      rw [hl]
      rfl
    · simp at hl
  | succ n =>
    -- a longer walk is `a :: l'`
    simp only [walks, Finset.mem_biUnion, Finset.mem_image] at hl
    obtain ⟨c, -, l', -, rfl⟩ := hl
    rfl
