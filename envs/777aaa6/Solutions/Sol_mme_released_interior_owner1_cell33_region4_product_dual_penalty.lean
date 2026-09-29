-- Prove2me | solution 1 for mme_released_interior_owner1_cell33_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:43.147992+00:00
-- url     : https://prove2.me/submissions/03c23cf7-2560-420e-838a-85011dcee7b0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 1 33 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(10664898842800000000000000000000000 / 3517713218767156271895480647920125183), (406886823704800000000000000000000000 / 3517713218767156271895480647920125183), (2629463627340400000000000000000000000 / 3517713218767156271895480647920125183), (45209599089800000000000000000000000 / 390857024307461807988386738657791687), (3554965868800000000000000000000000 / 1172571072922385423965160215973375061)], ![(6846695113 / 25000000000), (57432878899 / 40000000000), (143582132729 / 100000000000), (54773424117 / 200000000000), (1 / 1)], ![(78625508661 / 200000000000), (98281839693 / 250000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-724826067101 / 125000000000), (-107851566569 / 50000000000), (-291031243321 / 1000000000000), (-1078516196423 / 500000000000), (-289930432637 / 50000000000)], ![(-647554877137 / 500000000000), (18086874417 / 50000000000), (361737038991 / 1000000000000), (-259022450319 / 200000000000), (0 / 1)], ![(-933621182093 / 1000000000000), (-93362165149 / 100000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5798608536807 / 1000000000000), (-2157031331379 / 1000000000000), (-7275781083 / 25000000000), (-431406478569 / 200000000000), (-5798608652739 / 1000000000000)], ![(-1295109754273 / 1000000000000), (361737488341 / 1000000000000), (22608564937 / 62500000000), (-647556125797 / 500000000000), (0 / 1)], ![(-233405295523 / 250000000000), (-933621651489 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8027342441379 / 1000000000000), (-2192882382513 / 500000000000), (-682228985971 / 250000000000), (-862915386419 / 1000000000000), (-86291540647 / 100000000000), (-2728916086601 / 1000000000000), (-4385763798621 / 1000000000000), (-4013669794591 / 500000000000)] : List ℚ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-4013671220689 / 500000000000), (-175430590601 / 40000000000), (-2728915943883 / 1000000000000), (-431457693209 / 500000000000), (-862915406469 / 1000000000000), (-13644580433 / 5000000000), (-219288189931 / 50000000000), (-8027339589181 / 1000000000000)] : List ℚ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 1 33 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
