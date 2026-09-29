-- Prove2me | solution 1 for PRNGSeed.IsLinRec.ext_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:21:54.912884+00:00
-- url     : https://prove2.me/submissions/57d3b27c-f1d5-4c9c-a425-62442ad65e1a

import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
open PRNGSeed in
theorem solution {F : Type*} [CommRing F] {L : ℕ} {c : Fin L → F} {x y : ℕ → F}
    (hx : IsLinRec L c x) (hy : IsLinRec L c y) (h : ∀ i : ℕ, i < L → x i = y i) : x = y := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < L
    · exact h n hn
    · -- above the window the recurrence expresses `x n` from strictly earlier values
      obtain ⟨m, rfl⟩ : ∃ m, n = m + L := ⟨n - L, by omega⟩
      rw [hx m, hy m]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih (m + (i : ℕ)) (by have := i.isLt; omega)]
