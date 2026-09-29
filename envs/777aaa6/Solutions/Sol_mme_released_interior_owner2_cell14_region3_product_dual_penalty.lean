-- Prove2me | solution 1 for mme_released_interior_owner2_cell14_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:19:06.531518+00:00
-- url     : https://prove2.me/submissions/c0fd73b7-ae25-4988-b1e3-be39550248c1

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 2 14 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(597389219493 / 1000000000000), (119477796333 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (31004662846600000000000000000000000 / 1524948696514973048653930482373688583), (256759923683600000000000000000000000 / 508316232171657682884643494124562861), (770279467345000000000000000000000000 / 1524948696514973048653930482373688583), (31004621657600000000000000000000000 / 1524948696514973048653930482373688583)], ![(116472809283 / 200000000000), (1051184030829 / 1000000000000), (116472715879 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-515186419073 / 1000000000000), (-257593408593 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1947789219633 / 500000000000), (-682962258963 / 1000000000000), (-682962653243 / 1000000000000), (-779115953549 / 200000000000)], ![(-67582439687 / 125000000000), (2495858863 / 50000000000), (-108132063887 / 200000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4024893899 / 7812500000), (-103037363437 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-779115687853 / 200000000000), (-341481129481 / 500000000000), (-341481326621 / 500000000000), (-60868433871 / 15625000000)], ![(-108131903499 / 200000000000), (49917177261 / 1000000000000), (-270330159717 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-2475712787969 / 500000000000), (-54337781171 / 31250000000), (-143528987361 / 125000000000), (-229646379011 / 200000000000), (-434702246981 / 250000000000), (-4951425704307 / 1000000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4951425575937 / 1000000000000), (-1738808997471 / 1000000000000), (-1148231898887 / 1000000000000), (-574115947527 / 500000000000), (-1738808987923 / 1000000000000), (-2475712852153 / 500000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 2 14 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
