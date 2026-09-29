-- Prove2me | solution 1 for mme_released_interior_owner1_cell37_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:12:58.802283+00:00
-- url     : https://prove2.me/submissions/79f0fc4f-9799-4ca2-9e5b-48fb926fb5fb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 1 37 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (78713891299500000000000000000000000 / 3780038850862616983851721275663488339), (1904512114020500000000000000000000000 / 3780038850862616983851721275663488339), (1904511656314500000000000000000000000 / 3780038850862616983851721275663488339), (78713795619000000000000000000000000 / 3780038850862616983851721275663488339)], ![(73285533997 / 125000000000), (1045999138451 / 1000000000000), (293141975103 / 500000000000), (1 / 1), (1 / 1)], ![(149770890639 / 250000000000), (11981667889 / 20000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-967917479299 / 250000000000), (-342754209967 / 500000000000), (-685508660261 / 1000000000000), (-774334226549 / 200000000000)], ![(-53395050127 / 100000000000), (44972541981 / 1000000000000), (-5339510501 / 10000000000), (0 / 1), (0 / 1)], ![(-128088546791 / 250000000000), (-51235446777 / 100000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-774333983439 / 200000000000), (-685508419933 / 1000000000000), (-34275433013 / 50000000000), (-483958891593 / 125000000000)], ![(-533950501269 / 1000000000000), (22486270991 / 500000000000), (-533951050099 / 1000000000000), (0 / 1), (0 / 1)], ![(-512354187163 / 1000000000000), (-512354467769 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-491797543511 / 100000000000), (-865906828599 / 500000000000), (-28822258643 / 25000000000), (-1152890305441 / 1000000000000), (-1731813629299 / 1000000000000), (-4917975821223 / 1000000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4917975435109 / 1000000000000), (-1731813657197 / 1000000000000), (-1152890345719 / 1000000000000), (-7205564409 / 6250000000), (-865906814649 / 500000000000), (-2458987910611 / 500000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 1 37 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
