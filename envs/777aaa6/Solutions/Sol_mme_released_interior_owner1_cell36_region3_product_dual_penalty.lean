-- Prove2me | solution 1 for mme_released_interior_owner1_cell36_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:45.163635+00:00
-- url     : https://prove2.me/submissions/c0ffb997-c5bf-41f6-9664-64708292bdf5

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 1 36 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (78960028685000000000000000000000000 / 3775513415773928209914033131469880401), (633204114612500000000000000000000000 / 1258504471924642736638011043823293467), (1899606674522500000000000000000000000 / 3775513415773928209914033131469880401), (78959979029500000000000000000000000 / 3775513415773928209914033131469880401)], ![(599562872221 / 1000000000000), (29978059001 / 50000000000), (1 / 1), (1 / 1), (1 / 1)], ![(18327851039 / 31250000000), (1046609380019 / 1000000000000), (586487884093 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-966837474551 / 250000000000), (-171721635459 / 250000000000), (-686889526299 / 1000000000000), (-3867350527073 / 1000000000000)], ![(-999129757 / 1953125000), (-511557257979 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-21343902343 / 40000000000), (5694472161 / 125000000000), (-106720653817 / 200000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3867349898203 / 1000000000000), (-137377308367 / 200000000000), (-343444763149 / 500000000000), (-120854703971 / 31250000000)], ![(-511554435583 / 1000000000000), (-255778628989 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-266798779287 / 500000000000), (45555777289 / 1000000000000), (-133400817271 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4912510425339 / 1000000000000), (-1152888022521 / 1000000000000), (-346408849301 / 200000000000), (-433011085713 / 250000000000), (-288222046149 / 250000000000), (-4912502521241 / 1000000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-2456255212669 / 500000000000), (-28822200563 / 25000000000), (-216505530813 / 125000000000), (-1732044342851 / 1000000000000), (-230577636919 / 200000000000), (-122812563031 / 25000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 1 36 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
