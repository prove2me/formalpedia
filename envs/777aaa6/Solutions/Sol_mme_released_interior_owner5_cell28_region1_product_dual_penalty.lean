-- Prove2me | solution 1 for mme_released_interior_owner5_cell28_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:22:50.995016+00:00
-- url     : https://prove2.me/submissions/323596ca-87d6-4c68-a0fd-1bcbfaddf2d0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 5 28 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(69050873211 / 250000000000), (178203833709 / 125000000000), (178199241941 / 125000000000), (276174584221 / 1000000000000), (1 / 1)], ![(26652106747 / 500000000000), (2034898849171 / 1000000000000), (3294947104621 / 250000000000), (1017392693353 / 500000000000), (13326021387 / 250000000000)], ![(56249139377000000000000000000000000 / 2504953674522506741497414234446100603), (56247664046000000000000000000000000 / 2504953674522506741497414234446100603), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![5, -1, -3, -1, 5], ![6, 6, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1286617392019 / 1000000000000), (354614291021 / 1000000000000), (177294261873 / 500000000000), (-1286722061717 / 1000000000000), (0 / 1)], ![(-586347979703 / 200000000000), (177611528023 / 250000000000), (2578684475719 / 1000000000000), (142078070451 / 200000000000), (-45808473419 / 15625000000)], ![(-3796234779141 / 1000000000000), (-3796261007993 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-643308696009 / 500000000000), (177307145511 / 500000000000), (354588523747 / 1000000000000), (-321680515429 / 250000000000), (0 / 1)], ![(-1465869949257 / 500000000000), (710446112093 / 1000000000000), (64467111893 / 25000000000), (5549924627 / 7812500000), (-586348459763 / 200000000000)], ![(-189811738957 / 50000000000), (-474532625999 / 125000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([7, 2, 4, 12, 12, 4, 2, 7] : List ℤ).getD
    ((seed 5 28).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-273281920549 / 62500000000), (-215740444919 / 250000000000), (-136561506793 / 50000000000), (-801459447 / 100000000), (-1001840370999 / 125000000000), (-341403296519 / 125000000000), (-862962241251 / 1000000000000), (-34160062873 / 7812500000)] : List ℚ).getD
    ((seed 5 28).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4372510728783 / 1000000000000), (-34518471187 / 40000000000), (-2731230135859 / 1000000000000), (-8014594469999 / 1000000000000), (-8014722967991 / 1000000000000), (-2731226372151 / 1000000000000), (-690369793 / 800000000), (-4372488047743 / 1000000000000)] : List ℚ).getD
    ((seed 5 28).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 28 1 c : ℝ) / 1000000000000) ≤
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
