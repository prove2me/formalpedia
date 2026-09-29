-- Prove2me | solution 1 for mme_released_interior_owner2_cell28_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:32.793014+00:00
-- url     : https://prove2.me/submissions/8af87311-917a-40d8-a3e9-a62581d88084

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 2 28 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(279001185589 / 1000000000000), (1405589608381 / 1000000000000), (351399004183 / 250000000000), (8718893361 / 31250000000), (1 / 1)], ![(53068425589000000000000000000000000 / 17685735601289011964187637191763333641), (2005189608575000000000000000000000000 / 17685735601289011964187637191763333641), (4544305214703000000000000000000000000 / 5895245200429670654729212397254444547), (2005207592980000000000000000000000000 / 17685735601289011964187637191763333641), (53068436912000000000000000000000000 / 17685735601289011964187637191763333641)], ![(196027822717 / 500000000000), (392057419721 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1276539247747 / 1000000000000), (6809137297 / 20000000000), (34046142403 / 100000000000), (-638263527229 / 500000000000), (0 / 1)], ![(-1161786313141 / 200000000000), (-1088509896141 / 500000000000), (-130135639939 / 500000000000), (-2177010823393 / 1000000000000), (-5808931352339 / 1000000000000)], ![(-936351496629 / 1000000000000), (-936346971039 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-638269623873 / 500000000000), (340456864851 / 1000000000000), (340461424031 / 1000000000000), (-1276527054457 / 1000000000000), (0 / 1)], ![(-726116445713 / 125000000000), (-2177019792281 / 1000000000000), (-260271279877 / 1000000000000), (-68031588231 / 31250000000), (-2904465676169 / 500000000000)], ![(-234087874157 / 250000000000), (-468173485519 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 5, 7, 2, 2, 7, 5, 12] : List ℤ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-8021805591063 / 1000000000000), (-1386452669643 / 500000000000), (-4389898343359 / 1000000000000), (-428080693033 / 500000000000), (-34246454099 / 40000000000), (-2194948521099 / 500000000000), (-2772905455179 / 1000000000000), (-8021822095029 / 1000000000000)] : List ℚ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4010902795531 / 500000000000), (-554581067857 / 200000000000), (-2194949171679 / 500000000000), (-171232277213 / 200000000000), (-428080676237 / 500000000000), (-4389897042197 / 1000000000000), (-1386452727589 / 500000000000), (-2005455523757 / 250000000000)] : List ℚ).getD
    ((seed 2 28).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 2 28 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
