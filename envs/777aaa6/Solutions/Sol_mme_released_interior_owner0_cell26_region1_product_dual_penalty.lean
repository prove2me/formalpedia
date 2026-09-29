-- Prove2me | solution 1 for mme_released_interior_owner0_cell26_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T13:17:11.700983+00:00
-- url     : https://prove2.me/submissions/fd37ca51-551f-4581-bcff-83f2c6ee7691

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 0 26 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(82760447735500000000000000000000000 / 8108897143459576688632057130178745283), (1237168121643000000000000000000000000 / 8108897143459576688632057130178745283), (1237086710952000000000000000000000000 / 8108897143459576688632057130178745283), (82743869263500000000000000000000000 / 8108897143459576688632057130178745283), (1 / 1)], ![(55481628541 / 125000000000), (212414547941 / 250000000000), (443794539711 / 1000000000000), (1 / 1), (1 / 1)], ![(84827171633 / 500000000000), (1206377324999 / 500000000000), (1206297765289 / 500000000000), (42405279883 / 250000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-458476688771 / 100000000000), (-470034219169 / 250000000000), (-940101341453 / 500000000000), (-4584967226557 / 1000000000000), (0 / 1)], ![(-203065447157 / 250000000000), (-16292113771 / 100000000000), (-16247871441 / 20000000000), (0 / 1), (0 / 1)], ![(-443498046687 / 250000000000), (880769103063 / 1000000000000), (440351575807 / 500000000000), (-354837607567 / 200000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4584766887709 / 1000000000000), (-75205475067 / 40000000000), (-376040536581 / 200000000000), (-1146241806639 / 250000000000), (0 / 1)], ![(-812261788627 / 1000000000000), (-162921137709 / 1000000000000), (-812393572049 / 1000000000000), (0 / 1), (0 / 1)], ![(-1773992186747 / 1000000000000), (110096137883 / 125000000000), (176140630323 / 200000000000), (-887094018917 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-1623170014241 / 250000000000), (-4520453108593 / 1000000000000), (-447038774801 / 100000000000), (-290623552361 / 250000000000), (-1811227992207 / 1000000000000), (-1811227966481 / 1000000000000), (-581247032403 / 500000000000), (-223519473843 / 50000000000), (-4520455705781 / 1000000000000), (-6492684539687 / 1000000000000)] : List ℚ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-6492680056963 / 1000000000000), (-282528319287 / 62500000000), (-4470387748009 / 1000000000000), (-1162494209443 / 1000000000000), (-905613996103 / 500000000000), (-22640349581 / 12500000000), (-232498812961 / 200000000000), (-4470389476859 / 1000000000000), (-226022785289 / 50000000000), (-3246342269843 / 500000000000)] : List ℚ).getD
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
        (splitWeight 0 26 1 c : ℝ) / 1000000000000) ≤
          (1671 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1671 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1671 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
