-- Prove2me | solution 1 for mme_released_interior_owner1_cell32_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:40.630126+00:00
-- url     : https://prove2.me/submissions/b69bbcdf-fc8d-4afa-9157-6d2cc5b5764a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 1 32 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(38933216277000000000000000000000000 / 19702414772642478888574175139541567903), (2349610264422000000000000000000000000 / 19702414772642478888574175139541567903), (16567936851327000000000000000000000000 / 19702414772642478888574175139541567903), (2349815649092000000000000000000000000 / 19702414772642478888574175139541567903), (38933399955000000000000000000000000 / 19702414772642478888574175139541567903)], ![(101840974359 / 250000000000), (415568799683 / 500000000000), (407399239053 / 1000000000000), (1 / 1), (1 / 1)], ![(104359202729 / 250000000000), (792074544709 / 1000000000000), (417473020547 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-6226648709369 / 1000000000000), (-132905733503 / 62500000000), (-86635946461 / 500000000000), (-53160108191 / 25000000000), (-6226643991609 / 1000000000000)], ![(-56128024757 / 62500000000), (-184959914963 / 1000000000000), (-179592328601 / 200000000000), (0 / 1), (0 / 1)], ![(-436811048623 / 500000000000), (-23309976949 / 100000000000), (-54595959889 / 62500000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-6226648709367 / 1000000000000), (-2126491736047 / 1000000000000), (-173271892921 / 1000000000000), (-2126404327639 / 1000000000000), (-778330498951 / 125000000000)], ![(-898048396111 / 1000000000000), (-92479957481 / 500000000000), (-224490410751 / 250000000000), (0 / 1), (0 / 1)], ![(-174724419449 / 200000000000), (-233099769489 / 1000000000000), (-873535358223 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1599629141989 / 200000000000), (-130302125917 / 40000000000), (-796246752451 / 250000000000), (-972427816667 / 500000000000), (-295665788687 / 500000000000), (-388971129419 / 200000000000), (-796246584823 / 250000000000), (-3257552493861 / 1000000000000), (-399915724247 / 50000000000)] : List ℚ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-999768213743 / 125000000000), (-814388286981 / 250000000000), (-3184987009803 / 1000000000000), (-1944855633333 / 1000000000000), (-591331577373 / 1000000000000), (-972427823547 / 500000000000), (-3184986339291 / 1000000000000), (-162877624693 / 50000000000), (-7998314484939 / 1000000000000)] : List ℚ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 32 1 c : ℝ) / 1000000000000) ≤
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
