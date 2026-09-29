-- Prove2me | solution 1 for mme_released_interior_owner5_cell26_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:22:50.24768+00:00
-- url     : https://prove2.me/submissions/dcd759ec-2253-40b2-aaa9-30c5324517ab

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 5 26 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(171186245857 / 1000000000000), (2392280119003 / 1000000000000), (598026919091 / 250000000000), (171149500183 / 1000000000000), (1 / 1)], ![(22194746641 / 50000000000), (170042023163 / 200000000000), (88766196827 / 200000000000), (1 / 1), (1 / 1)], ![(32879909448200000000000000000000000 / 3240948510473191691048952077880681597), (55380883535200000000000000000000000 / 360105390052576854560994675320075733), (166130695887200000000000000000000000 / 1080316170157730563682984025960227199), (3652524548800000000000000000000000 / 360105390052576854560994675320075733), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1765003158123 / 1000000000000), (436123467919 / 500000000000), (872174850277 / 1000000000000), (-353043566871 / 200000000000), (0 / 1)], ![(-406083691173 / 500000000000), (-162271764969 / 1000000000000), (-162462291077 / 200000000000), (0 / 1), (0 / 1)], ![(-2295379749957 / 500000000000), (-187216226709 / 100000000000), (-1872234224221 / 1000000000000), (-2295489076519 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-882501579061 / 500000000000), (872246935839 / 1000000000000), (436087425139 / 500000000000), (-882608917177 / 500000000000), (0 / 1)], ![(-162433476469 / 200000000000), (-20283970621 / 125000000000), (-101538931923 / 125000000000), (0 / 1), (0 / 1)], ![(-4590759499913 / 1000000000000), (-1872162267089 / 1000000000000), (-93611711211 / 50000000000), (-4590978153037 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-1622513020839 / 250000000000), (-4534823427181 / 1000000000000), (-4453167417071 / 1000000000000), (-1162394168583 / 1000000000000), (-3538495753 / 1953125000), (-1811709795201 / 1000000000000), (-290598510157 / 250000000000), (-111329219069 / 25000000000), (-566853239663 / 125000000000), (-1298011210103 / 200000000000)] : List ℚ).getD
    ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-1298010416671 / 200000000000), (-226741171359 / 50000000000), (-445316741707 / 100000000000), (-581197084291 / 500000000000), (-362341965107 / 200000000000), (-566159311 / 312500000), (-1162394040627 / 1000000000000), (-4453168762759 / 1000000000000), (-4534825917303 / 1000000000000), (-3245028025257 / 500000000000)] : List ℚ).getD
    ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 26 1 c : ℝ) / 1000000000000) ≤
          (1564 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1564 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1564 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
