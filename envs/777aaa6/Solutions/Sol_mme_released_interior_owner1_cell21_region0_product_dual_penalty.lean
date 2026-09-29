-- Prove2me | solution 1 for mme_released_interior_owner1_cell21_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:51.610677+00:00
-- url     : https://prove2.me/submissions/cab461b8-ca9a-409b-ba78-a7a1d18a1335

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 1 21 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(411023678555000000000000000000000000 / 19838753472739101543642362934218501171), (810625616989000000000000000000000000 / 19838753472739101543642362934218501171), (411025624514000000000000000000000000 / 19838753472739101543642362934218501171), (1 / 1), (1 / 1)], ![(2436898287 / 62500000000), (2312727556243 / 1000000000000), (16896205798339 / 1000000000000), (1156369294289 / 500000000000), (38990377577 / 1000000000000)], ![(206388218273 / 500000000000), (804256109951 / 1000000000000), (20638919161 / 50000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1938370862489 / 500000000000), (-3197586233673 / 1000000000000), (-484592123821 / 125000000000), (0 / 1), (0 / 1)], ![(-1622220259971 / 500000000000), (419213794131 / 500000000000), (2827089087749 / 1000000000000), (838432358521 / 1000000000000), (-324444039209 / 100000000000)], ![(-176969829691 / 200000000000), (-217837515813 / 1000000000000), (-884844432417 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3876741724977 / 1000000000000), (-399698279209 / 125000000000), (-3876736990567 / 1000000000000), (0 / 1), (0 / 1)], ![(-3244440519941 / 1000000000000), (838427588263 / 1000000000000), (11308356351 / 4000000000), (419216179261 / 500000000000), (-3244440392089 / 1000000000000)], ![(-442424574227 / 500000000000), (-54459378953 / 250000000000), (-27651388513 / 31250000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8006031265207 / 1000000000000), (-1628073441731 / 500000000000), (-77379882773 / 40000000000), (-3244003022431 / 1000000000000), (-73541832717 / 125000000000), (-324400307901 / 100000000000), (-967248525797 / 500000000000), (-3256146916937 / 1000000000000), (-4003010970693 / 500000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-4003015632603 / 500000000000), (-3256146883461 / 1000000000000), (-483624267331 / 250000000000), (-324400302243 / 100000000000), (-117666932347 / 200000000000), (-3244003079009 / 1000000000000), (-1934497051593 / 1000000000000), (-407018364617 / 125000000000), (-1601204388277 / 200000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 1 21 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
