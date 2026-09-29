-- Prove2me | solution 1 for mme_released_global_owner3_cell35_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T05:09:24.150804+00:00
-- url     : https://prove2.me/submissions/63d991f4-c589-4bd0-9d60-34c8e3052930

import Theorems.Thm_mme_rational_boundary_volume_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Theorems.Thm_mme_released_global_word_counts_row_marginal
import Definitions.Def_mme_recursive_yz_boundary_data

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed
open MME.ReleasedGlobal MME.RecursiveYZ.Boundary

private def wordIndex (w : Word) : ℕ :=
  27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val

private def massNumerator (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 53433261809794023472000000000000000000000000000000000000, 0, 53433261752327145688000000000000000000000000000000000000, 0, 0, 0, 47713552795795392744000000000000000000000000000000000000, 0, 1048366241528617130528000000000000000000000000000000000000, 0, 47713552805373205708000000000000000000000000000000000000, 0, 0, 0, 47713552599450226982000000000000000000000000000000000000, 0, 47713552599450226982000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 47713552805373205708000000000000000000000000000000000000, 0, 1048366238023137585704000000000000000000000000000000000000, 0, 47713552805373205708000000000000000000000000000000000000, 0, 0, 0, 1048366209984090133594000000000000000000000000000000000000, 0, 1048366210300157961406000000000000000000000000000000000000, 0, 0, 0, 0, 0, 53433318496080050906000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47713552599450226982000000000000000000000000000000000000, 0, 47713552599450226982000000000000000000000000000000000000, 0, 0, 0, 0, 0, 53433318496080050906000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def logScale (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def lowerMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 4495623940095, 0, 4495623941170, 0, 0, 0, 4608841889249, 0, 1519069101546, 0, 4608841889048, 0, 0, 0, 4608841893364, 0, 4608841893364, 0, 0, 0, 0, 0, 0, 0, 4608841889048, 0, 1519069104890, 0, 4608841889048, 0, 0, 0, 1519069131635, 0, 1519069131334, 0, 0, 0, 0, 0, 4495622879215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4608841893364, 0, 4608841893364, 0, 0, 0, 0, 0, 4495622879215, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def upperMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 4495623940094, 0, 4495623941169, 0, 0, 0, 4608841889248, 0, 1519069101545, 0, 4608841889047, 0, 0, 0, 4608841893363, 0, 4608841893363, 0, 0, 0, 0, 0, 0, 0, 4608841889047, 0, 1519069104889, 0, 4608841889047, 0, 0, 0, 1519069131634, 0, 1519069131333, 0, 0, 0, 0, 0, 4495622879214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4608841893363, 0, 4608841893363, 0, 0, 0, 0, 0, 4495622879214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def x (z : Fin 3) (w : Word) : ℚ :=
  (massNumerator z w : ℚ) / 1000000000000000000000000000000000000000000000000000000000000
private def lower (z : Fin 3) (w : Word) : ℚ := -(lowerMagnitude z w : ℚ) / 1000000000000
private def upper (z : Fin 3) (w : Word) : ℚ := -(upperMagnitude z w : ℚ) / 1000000000000
private def bound (z : Fin 3) : ℚ := ((![0, 30295951027, 0] : Fin 3 → ℕ) z : ℚ) / 1000000000000

private theorem log_bounds (z : Fin 3) (w : Word)
    (hp : 0 < x z w / ∑ v, x z v) :
    (lower z w : ℝ) ≤ Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ∧
      Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ≤ (upper z w : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale z w) 16
  all_goals revert z w; decide +kernel

/-- A released outer boundary cell has a certified free-mode entropy and
letter-volume lower bound, with the actual global coarse weight included. -/
theorem solution
    (z : Fin 3) (hz : ((shape 35).val z).val = 0) :
    (denominator : ℝ) ^ 5 * (((![0, 30295951027, 0] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 3 (z + 1) (shapeEquiv 35) w : ℝ)) +
        (∑ w, (wordCounts 3 (z + 1) (shapeEquiv 35) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ z w, 0 ≤ x z w := by decide +kernel
  have hcert : ∀ z, bound z ≤
      (∑ w, x z w) * (-(∑ w, (x z w / ∑ v, x z v) * upper z w)) +
        (∑ w, x z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x z) (hx z) ones
    (lower z) (upper z) (log_bounds z) (bound z) (hcert z)
    ((denominator : ℝ) ^ 5) (by positivity)
  have hid : ∀ z : Fin 3, ((shape 35).val z).val = 0 → ∀ w : Word,
      (denominator : ℚ) ^ 5 * x z w = (alpha 3 35 * ((jointRows 3 35).map
        (fun a => if atom a.1 (z + 1) = w then a.2 else 0)).sum : ℕ) := by
    decide +kernel
  have he (w : Word) :
      (denominator : ℝ) ^ 5 * (x z w : ℝ) = (wordCounts 3 (z + 1) (shapeEquiv 35) w : ℝ) := by
    rw [mme_released_global_word_counts_row_marginal, Equiv.symm_apply_apply]
    have hh := congrArg (fun q : ℚ => (q : ℝ)) (hid z hz w)
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at hh
    exact hh
  simp_rw [he] at h
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
