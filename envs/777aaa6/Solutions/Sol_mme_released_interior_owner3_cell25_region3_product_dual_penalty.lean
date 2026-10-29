-- Prove2me | solution 1 for mme_released_interior_owner3_cell25_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:14:53.378733+00:00
-- url     : https://prove2.me/submissions/a3449fb3-2b21-4a66-a55a-0d0660dcd3c5

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 3 25 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(4671792978917053282070210829 / 25000000000000000000000000000), (94915950250180950840497498181 / 100000000000000000000000000000), (94915921863448350840781365507 / 100000000000000000000000000000), (934361639357290656383606427 / 5000000000000000000000000000), (1 / 1)], ![(50000005938226599999940617729 / 100000000000000000000000000000), (24999997030886450000029691133 / 50000000000000000000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(173954118466698260458815333 / 50000000000000000000000000000), (12963253004277570367469957223 / 100000000000000000000000000000), (11221551317130187784486828697 / 12500000000000000000000000000), (12963252348910970367476510889 / 100000000000000000000000000000), (347908465614896520915343851 / 100000000000000000000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![1, 1, 0, 0, 0], ![8, 3, 0, 3, 8]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-335466578268701 / 200000000000000), (-52178420204479 / 1000000000000000), (-10435743855367 / 200000000000000), (-419332408488757 / 250000000000000), (0 / 1)], ![(-693147061795421 / 1000000000000000), (-138629459864899 / 200000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-5660986706940279 / 1000000000000000), (-510762880785893 / 250000000000000), (-10789249021239 / 100000000000000), (-408610314739859 / 200000000000000), (-226439441985457 / 40000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-838666445671751 / 500000000000000), (-26089210102239 / 500000000000000), (-26089359638417 / 500000000000000), (-67093185358201 / 40000000000000), (0 / 1)], ![(-693147061795419 / 1000000000000000), (-693147299324493 / 1000000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-5660986706940271 / 1000000000000000), (-2043051523143569 / 1000000000000000), (-107892490212389 / 1000000000000000), (-2043051573699291 / 1000000000000000), (-2830493024818209 / 500000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 4, 6, 1, 1, 6, 4, 12] : List ℤ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-1003932955027457 / 125000000000000), (-2788377541744869 / 1000000000000000), (-441352821889399 / 100000000000000), (-426609104870667 / 500000000000000), (-853218271284617 / 1000000000000000), (-2206765882183629 / 500000000000000), (-1394188527849581 / 500000000000000), (-160629320055509 / 20000000000000)] : List ℚ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-1606292728043929 / 200000000000000), (-557675508348973 / 200000000000000), (-882705643778797 / 200000000000000), (-213304552435333 / 250000000000000), (-170643654256923 / 200000000000000), (-1103382941091813 / 250000000000000), (-1394188527849579 / 500000000000000), (-8031466002775439 / 1000000000000000)] : List ℚ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 3 25 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
