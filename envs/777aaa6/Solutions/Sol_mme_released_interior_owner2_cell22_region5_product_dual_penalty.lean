-- Prove2me | solution 1 for mme_released_interior_owner2_cell22_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:40:30.509065+00:00
-- url     : https://prove2.me/submissions/8043cca2-5bd5-4bdd-a592-e0cb9f778144

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 2 22 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(116440869441 / 200000000000), (1051590048097 / 1000000000000), (58220494893 / 100000000000), (1 / 1), (1 / 1)], ![(1 / 1), (31017513598600000000000000000000000 / 1525194852592221965078636660068220009), (769886067304000000000000000000000000 / 1525194852592221965078636660068220009), (109983781317000000000000000000000000 / 217884978941745995011233808581174287), (31017493573400000000000000000000000 / 1525194852592221965078636660068220009)], ![(597696080343 / 1000000000000), (597696398759 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-540933780841 / 1000000000000), (25151675123 / 500000000000), (-33808296707 / 62500000000), (0 / 1), (0 / 1)], ![(0 / 1), (-97383136333 / 25000000000), (-42727182107 / 62500000000), (-683634391667 / 1000000000000), (-3895326098929 / 1000000000000)], ![(-257336440537 / 500000000000), (-102934469667 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-13523344521 / 25000000000), (50303350247 / 1000000000000), (-540932747311 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3895325453319 / 1000000000000), (-683634913711 / 1000000000000), (-341817195833 / 500000000000), (-243457881183 / 62500000000)], ![(-514672881073 / 1000000000000), (-257336174167 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-2475465274489 / 500000000000), (-5740019559 / 5000000000), (-1739240542099 / 1000000000000), (-1739240520841 / 1000000000000), (-574001961247 / 500000000000), (-99018655217 / 20000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4950930548977 / 1000000000000), (-1148003911799 / 1000000000000), (-869620271049 / 500000000000), (-43481013021 / 25000000000), (-1148003922493 / 1000000000000), (-4950932760849 / 1000000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 2 22 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
