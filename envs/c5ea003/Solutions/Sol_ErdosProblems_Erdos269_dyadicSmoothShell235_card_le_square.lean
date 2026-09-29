-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicSmoothShell235_card_le_square
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:43:58.098197+00:00
-- url     : https://prove2.me/submissions/84539546-f926-4b3f-800c-3b11e7211e1d

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Theorems.Thm_ErdosProblems_Erdos269_exponent_unique_in_short_interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: summability of the actual dyadic shell masses

The ordered source digit has a deliberately coarse quadratic majorant.  The
key point is structural: in a multiplicative interval of width two, fixing the
`3`- and `5`-exponents determines the `2`-exponent, while both odd exponents
are smaller than the dyadic scale.  This gives at most `(a+1)^2` shell points.
-/

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (a : ℕ) :
    (dyadicSmoothShell235 a).card ≤ (a + 1) ^ 2 := by
  classical
  let target := (Finset.range (a + 1)).product (Finset.range (a + 1))
  have hcard : (dyadicSmoothShell235 a).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ × ℕ => e.2) ?_ ?_
    · intro e he
      rcases e with ⟨i, j, k⟩
      have hshell := mem_dyadicSmoothShell235_iff.mp he
      change 2 ^ a ≤ smooth3Val 2 3 5 i j k ∧
        smooth3Val 2 3 5 i j k < 2 ^ (a + 1) at hshell
      have hpos : 0 < smooth3Val 2 3 5 i j k := by
        simp [smooth3Val]
      have hjDvd : 3 ^ j ∣ smooth3Val 2 3 5 i j k := by
        refine ⟨2 ^ i * 5 ^ k, ?_⟩
        simp [smooth3Val]
        ring
      have hkDvd : 5 ^ k ∣ smooth3Val 2 3 5 i j k := by
        refine ⟨2 ^ i * 3 ^ j, ?_⟩
        simp [smooth3Val]
        ring
      have hj : j < a + 1 := by
        by_contra hnot
        have haj : a + 1 ≤ j := Nat.le_of_not_gt hnot
        have hpowExp : 2 ^ (a + 1) ≤ 2 ^ j :=
          Nat.pow_le_pow_right (by norm_num) haj
        have hpowBase : 2 ^ j ≤ 3 ^ j :=
          Nat.pow_le_pow_left (by norm_num) j
        have hdivLe := Nat.le_of_dvd hpos hjDvd
        exact (not_lt_of_ge (hpowExp.trans (hpowBase.trans hdivLe))) hshell.2
      have hk : k < a + 1 := by
        by_contra hnot
        have hak : a + 1 ≤ k := Nat.le_of_not_gt hnot
        have hpowExp : 2 ^ (a + 1) ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by norm_num) hak
        have hpowBase : 2 ^ k ≤ 5 ^ k :=
          Nat.pow_le_pow_left (by norm_num) k
        have hdivLe := Nat.le_of_dvd hpos hkDvd
        exact (not_lt_of_ge (hpowExp.trans (hpowBase.trans hdivLe))) hshell.2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩
    · intro e₁ he₁ e₂ he₂ hproj
      rcases e₁ with ⟨i₁, j₁, k₁⟩
      rcases e₂ with ⟨i₂, j₂, k₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      have hshell₁ := mem_dyadicSmoothShell235_iff.mp he₁
      have hshell₂ := mem_dyadicSmoothShell235_iff.mp he₂
      have hi : i₁ = i₂ := exponent_unique_in_short_interval
        (base := 2) (lo := 2 ^ a) (hi := 2 ^ (a + 1))
        (weight := 3 ^ j₁ * 5 ^ k₁)
        (by norm_num)
        (by rw [pow_succ]; simp [Nat.mul_comm])
        (by simpa [smooth3Val, mul_assoc] using hshell₁.1)
        (by simpa [smooth3Val, mul_assoc] using hshell₁.2)
        (by simpa [smooth3Val, mul_assoc] using hshell₂.1)
        (by simpa [smooth3Val, mul_assoc] using hshell₂.2)
      simp [hi]
  simpa [target, pow_two] using hcard
