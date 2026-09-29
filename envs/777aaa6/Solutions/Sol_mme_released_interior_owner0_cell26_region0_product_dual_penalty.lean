-- Prove2me | solution 1 for mme_released_interior_owner0_cell26_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:27.528954+00:00
-- url     : https://prove2.me/submissions/e0f4373b-34f2-4de2-ae54-8cc610995448

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 0 26 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(33945509908400000000000000000000000 / 3176234685877568588381852666055784713), (162597406877400000000000000000000000 / 1058744895292522862793950888685261571), (487765618442800000000000000000000000 / 3176234685877568588381852666055784713), (33939892054600000000000000000000000 / 3176234685877568588381852666055784713), (1 / 1)], ![(444988680661 / 1000000000000), (172975973873 / 200000000000), (55617512647 / 125000000000), (1 / 1), (1 / 1)], ![(4375371787 / 25000000000), (2362381405473 / 1000000000000), (2362252427153 / 1000000000000), (34997246057 / 200000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4538695123929 / 1000000000000), (-374712435077 / 200000000000), (-74944668511 / 40000000000), (-1134715158463 / 250000000000), (0 / 1)], ![(-809706433857 / 1000000000000), (-72582330521 / 500000000000), (-32392624399 / 40000000000), (0 / 1), (0 / 1)], ![(-108930270549 / 62500000000), (26864693137 / 31250000000), (171923116431 / 200000000000), (-1743047992241 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-567336890491 / 125000000000), (-234195271923 / 125000000000), (-936808356387 / 500000000000), (-4538860633851 / 1000000000000), (0 / 1)], ![(-12651663029 / 15625000000), (-145164661041 / 1000000000000), (-404907804987 / 500000000000), (0 / 1), (0 / 1)], ![(-1742884328783 / 1000000000000), (171934036077 / 200000000000), (214903895539 / 250000000000), (-21788099903 / 12500000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-6413093742017 / 1000000000000), (-4490900042831 / 1000000000000), (-276762484989 / 62500000000), (-1159182961533 / 1000000000000), (-1823428897801 / 1000000000000), (-1823428857311 / 1000000000000), (-231836580177 / 200000000000), (-2214099902449 / 500000000000), (-1122725444117 / 250000000000), (-641309560001 / 100000000000)] : List ℚ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-100204589719 / 15625000000), (-449090004283 / 100000000000), (-4428199759823 / 1000000000000), (-289795740383 / 250000000000), (-9117144489 / 5000000000), (-182342885731 / 100000000000), (-289795725221 / 250000000000), (-4428199804897 / 1000000000000), (-4490901776467 / 1000000000000), (-6413095600009 / 1000000000000)] : List ℚ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 26 0 c : ℝ) / 1000000000000) ≤
          (414 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (414 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((414 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
