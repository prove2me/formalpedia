-- Prove2me | solution 1 for mme_released_interior_owner2_cell26_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:40:42.447002+00:00
-- url     : https://prove2.me/submissions/85e9653b-9d3e-4a1e-9ae9-4933bdf2775b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 2 26 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(171267314023 / 1000000000000), (478594730667 / 200000000000), (1196349190987 / 500000000000), (42802588613 / 250000000000), (1 / 1)], ![(443710315256000000000000000000000000 / 16209765724908285886163285352537586761), (283283534149000000000000000000000000 / 5403255241636095295387761784179195587), (147869528371000000000000000000000000 / 5403255241636095295387761784179195587), (1 / 1), (1 / 1)], ![(164504939657 / 1000000000000), (623341906441 / 250000000000), (155817681863 / 62500000000), (32889193367 / 200000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1764529703167 / 1000000000000), (3408346871 / 3906250000), (436210879591 / 500000000000), (-441215583873 / 250000000000), (0 / 1)], ![(-179909862787 / 50000000000), (-368538573739 / 125000000000), (-3598426553557 / 1000000000000), (0 / 1), (0 / 1)], ![(-902407340459 / 500000000000), (114204282109 / 125000000000), (913520061031 / 1000000000000), (-1805173231823 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-882264851583 / 500000000000), (872536798977 / 1000000000000), (872421759183 / 1000000000000), (-1764862335491 / 1000000000000), (0 / 1)], ![(-3598197255739 / 1000000000000), (-2948308589911 / 1000000000000), (-899606638389 / 250000000000), (0 / 1), (0 / 1)], ![(-1804814680917 / 1000000000000), (913634256873 / 1000000000000), (114190007629 / 125000000000), (-902586615911 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-2267380561081 / 500000000000), (-226467300679 / 125000000000), (-278315327681 / 62500000000), (-6489818591997 / 1000000000000), (-290596682939 / 250000000000), (-581193786253 / 500000000000), (-811224088727 / 125000000000), (-556632006797 / 125000000000), (-362347693517 / 200000000000), (-1133686737427 / 250000000000)] : List ℚ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4534761122161 / 1000000000000), (-1811738405431 / 1000000000000), (-890609048579 / 200000000000), (-1622454647999 / 250000000000), (-232477346351 / 200000000000), (-232477514501 / 200000000000), (-1297958541963 / 200000000000), (-7124889687 / 1600000000), (-7077103389 / 3906250000), (-4534746949707 / 1000000000000)] : List ℚ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 2 26 5 c : ℝ) / 1000000000000) ≤
          (1564 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1564 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1564 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
