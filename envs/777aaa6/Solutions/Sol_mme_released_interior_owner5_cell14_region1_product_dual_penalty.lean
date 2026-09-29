-- Prove2me | solution 1 for mme_released_interior_owner5_cell14_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:20:36.074848+00:00
-- url     : https://prove2.me/submissions/747a97b3-43a6-4bc0-ae29-fddcf67e95d1

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 5 14 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(597488234953 / 1000000000000), (149407522973 / 250000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (77594430221 / 500000000000), (961591855061 / 250000000000), (3847329038639 / 1000000000000), (15519985549 / 100000000000)], ![(145384159424250000000000000000000000 / 1906474206751230928468232759461872871), (263396226740500000000000000000000000 / 1906474206751230928468232759461872871), (145453665142000000000000000000000000 / 1906474206751230928468232759461872871), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-257510342913 / 500000000000), (-25739164593 / 50000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-58222264041 / 31250000000), (168391146961 / 125000000000), (1347379151341 / 1000000000000), (-372608320471 / 200000000000)], ![(-80425976117 / 31250000000), (-1979351386097 / 1000000000000), (-1286576633417 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-20600827433 / 40000000000), (-514783291859 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1863112449311 / 1000000000000), (1347129175689 / 1000000000000), (673689575671 / 500000000000), (-931520801177 / 500000000000)], ![(-2573631235743 / 1000000000000), (-123709461631 / 62500000000), (-2573153266833 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-87051768813 / 50000000000), (-4951693523999 / 1000000000000), (-1147005502267 / 1000000000000), (-573496460289 / 500000000000), (-4951049008059 / 1000000000000), (-69641791079 / 40000000000)] : List ℚ).getD
    ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-1741035376259 / 1000000000000), (-2475846761999 / 500000000000), (-573502751133 / 500000000000), (-1146992920577 / 1000000000000), (-4951049008057 / 1000000000000), (-870522388487 / 500000000000)] : List ℚ).getD
    ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 5 14 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
