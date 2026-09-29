-- Prove2me | solution 1 for RademacherWigner.sum_indC
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:17:39.037425+00:00
-- url     : https://prove2.me/submissions/9ca72916-a270-4e50-83ed-7b12efffb2b1

/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

Port of the proof in Paul Klemstine's Aether Catalog, commit 53c2925a02:
Catalog/Probability/WignerRademacherEnsemble.lean, lines 314–330 and 354–365.
The equality-indicator helper is imported from its Proved public target;
the unpublished inequality-indicator helpers are reproduced below.
-/
import Definitions.Def_Probability_WignerRademacherEnsemble
import Theorems.Thm_RademacherWigner_sum_indicator_eq_one

set_option autoImplicit false

open Matrix BigOperators Finset RademacherWigner

namespace DiscoveryWignerPort

private theorem sum_indicator_ne {N : ℕ} (i : Fin N) :
    (∑ j : Fin N, (if j = i then (0:ℝ) else 1)) = (N:ℝ) - 1 := by
  have hN : 1 ≤ N := lt_of_le_of_lt (Nat.zero_le i) i.isLt
  simp [Finset.sum_ite, Finset.filter_ne', Nat.cast_sub hN]

private theorem sum_indicator_ne' {N : ℕ} (i : Fin N) :
    (∑ j : Fin N, (if i = j then (0:ℝ) else 1)) = (N:ℝ) - 1 := by
  have h : (∑ j : Fin N, (if i = j then (0:ℝ) else 1))
      = ∑ j : Fin N, (if j = i then (0:ℝ) else 1) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, Ne.symm hj]
  rw [h, sum_indicator_ne]

end DiscoveryWignerPort

theorem solution(N : ℕ) :
    (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, indC i j k l)
      = (N:ℝ) * ((N:ℝ) - 1) := by
  have key : ∀ i j : Fin N,
      (∑ k : Fin N, ∑ l : Fin N, indC i j k l) = (if i = j then (0:ℝ) else 1) := by
    intro i j
    simp_rw [indC, ← Finset.mul_sum, sum_indicator_eq_one, mul_one]
    rw [← Finset.mul_sum, sum_indicator_eq_one, mul_one]
  simp_rw [key]
  rw [Finset.sum_congr rfl fun i _ => DiscoveryWignerPort.sum_indicator_ne' i]
  simp [Finset.card_univ]
  ring
