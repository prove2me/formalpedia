-- Prove2me | solution 1 for mme_released_interior_owner4_cell32_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:18:33.255509+00:00
-- url     : https://prove2.me/submissions/de595714-e0b3-44e5-8a6a-c3e208a54e16

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 4 32 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(39025246787 / 1000000000000), (2332751512523 / 1000000000000), (519720320211 / 31250000000), (1166373060021 / 500000000000), (19512622493 / 500000000000)], ![(403836898666000000000000000000000000 / 19733526704020041190987458498113163787), (845222381617000000000000000000000000 / 19733526704020041190987458498113163787), (403835972580000000000000000000000000 / 19733526704020041190987458498113163787), (1 / 1), (1 / 1)], ![(420396030231 / 1000000000000), (778842456391 / 1000000000000), (420395065247 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3243546488783 / 1000000000000), (423524238759 / 500000000000), (1405635722477 / 500000000000), (6776369327 / 8000000000), (-3243546534933 / 1000000000000)], ![(-1944531625537 / 500000000000), (-1575237282551 / 500000000000), (-777813108859 / 200000000000), (0 / 1), (0 / 1)], ![(-433279041431 / 500000000000), (-249946491831 / 1000000000000), (-866560378281 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1621773244391 / 500000000000), (847048477519 / 1000000000000), (562254288991 / 200000000000), (211761541469 / 250000000000), (-810886633733 / 250000000000)], ![(-3889063251073 / 1000000000000), (-3150474565101 / 1000000000000), (-1944532772147 / 500000000000), (0 / 1), (0 / 1)], ![(-866558082861 / 1000000000000), (-24994649183 / 100000000000), (-21664009457 / 25000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 4 32).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1599833573759 / 200000000000), (-3291963640421 / 1000000000000), (-972176083963 / 500000000000), (-158499321299 / 50000000000), (-589149611979 / 1000000000000), (-3169986521971 / 1000000000000), (-972176099339 / 500000000000), (-3291963495211 / 1000000000000), (-1599834482197 / 200000000000)] : List ℚ).getD
    ((seed 4 32).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-3999583934397 / 500000000000), (-164598182021 / 50000000000), (-77774086717 / 40000000000), (-3169986425979 / 1000000000000), (-294574805989 / 500000000000), (-316998652197 / 100000000000), (-1944352198677 / 1000000000000), (-329196349521 / 100000000000), (-999896551373 / 125000000000)] : List ℚ).getD
    ((seed 4 32).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 4 32 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
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
