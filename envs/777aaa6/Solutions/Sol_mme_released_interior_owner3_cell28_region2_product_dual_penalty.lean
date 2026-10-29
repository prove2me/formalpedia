-- Prove2me | solution 1 for mme_released_interior_owner3_cell28_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:15:38.344525+00:00
-- url     : https://prove2.me/submissions/a7b6ca64-3d4a-479d-a0b4-75bd134a93d2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 3 28 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(3645635645159663543643548403 / 20000000000000000000000000000), (11849429140695781505708593041 / 12500000000000000000000000000), (94795479700404752045202995943 / 100000000000000000000000000000), (18228120347452117718796525477 / 100000000000000000000000000000), (1 / 1)], ![(72085422539299279145774607 / 20000000000000000000000000000), (687661085619693123389143803 / 5000000000000000000000000000), (89023160123569809768398764293 / 100000000000000000000000000000), (3438306328746065616936712539 / 25000000000000000000000000000), (360435235596896395647644031 / 100000000000000000000000000000)], ![(24999994850452050000051495477 / 50000000000000000000000000000), (25000005149548449999948504513 / 50000000000000000000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![8, 3, 0, 3, 8], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-425550383762603 / 250000000000000), (-6681118958557 / 125000000000000), (-6681057543643 / 125000000000000), (-1702204710268329 / 1000000000000000), (0 / 1)], ![(-2812817856304053 / 500000000000000), (-1983897082965043 / 1000000000000000), (-116273624001367 / 1000000000000000), (-991948410509939 / 500000000000000), (-5625613175988127 / 1000000000000000)], ![(-138629477308377 / 200000000000000), (-693146974578029 / 1000000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-170220153505041 / 100000000000000), (-10689790333691 / 200000000000000), (-53448460349143 / 1000000000000000), (-851102355134163 / 500000000000000), (0 / 1)], ![(-2812817856304049 / 500000000000000), (-1983897082965039 / 1000000000000000), (-58136812000683 / 500000000000000), (-991948410509937 / 500000000000000), (-5625613175988119 / 1000000000000000)], ![(-173286846635471 / 250000000000000), (-173286743644507 / 250000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 4, 1, 6, 6, 1, 4, 12] : List ℤ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-8020962097580519 / 1000000000000000), (-2730493159230189 / 1000000000000000), (-215717367723091 / 250000000000000), (-2189624589887611 / 500000000000000), (-4379245330648287 / 1000000000000000), (-431434775123911 / 500000000000000), (-341311564736523 / 125000000000000), (-4010493698727153 / 500000000000000)] : List ℚ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-2005240524395127 / 250000000000000), (-546098631846037 / 200000000000000), (-862869470892363 / 1000000000000000), (-273703073735951 / 62500000000000), (-4379245330648281 / 1000000000000000), (-43143477512391 / 50000000000000), (-2730492517892179 / 1000000000000000), (-1002623424681787 / 125000000000000)] : List ℚ).getD
    ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 3 28 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
