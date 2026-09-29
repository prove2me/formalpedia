-- Prove2me | solution 1 for mme_released_global_owner0_cell29_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T04:14:37.874606+00:00
-- url     : https://prove2.me/submissions/eb38ecb8-d542-4574-aeee-128a2ac8fbee

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
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 56493932494981972288000000000000000000000000000000000000, 0, 56493932471386573698000000000000000000000000000000000000, 0, 0, 0, 52390982266507867358000000000000000000000000000000000000, 0, 1018494099478215208878000000000000000000000000000000000000, 0, 52390982252350628204000000000000000000000000000000000000, 0, 0, 0, 52390976664960242092000000000000000000000000000000000000, 0, 52390976669679321810000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 52390982200440751306000000000000000000000000000000000000, 0, 1018494099742483673086000000000000000000000000000000000000, 0, 52390982271226947076000000000000000000000000000000000000, 0, 0, 0, 1018494073098559585258000000000000000000000000000000000000, 0, 1018494071937665974630000000000000000000000000000000000000, 0, 0, 0, 0, 0, 56493836626877501118000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52390976669679321810000000000000000000000000000000000000, 0, 52390976669679321810000000000000000000000000000000000000, 0, 0, 0, 0, 0, 56493836485305109578000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def logScale (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def lowerMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 4425235841654, 0, 4425235842071, 0, 0, 0, 4500634602204, 0, 1533288642265, 0, 4500634602474, 0, 0, 0, 4500634709122, 0, 4500634709032, 0, 0, 0, 0, 0, 0, 0, 4500634603465, 0, 1533288642005, 0, 4500634602113, 0, 0, 0, 1533288668165, 0, 1533288669305, 0, 0, 0, 0, 0, 4425237538618, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4500634709032, 0, 4500634709032, 0, 0, 0, 0, 0, 4425237541124, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def upperMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 4425235841653, 0, 4425235842070, 0, 0, 0, 4500634602203, 0, 1533288642264, 0, 4500634602473, 0, 0, 0, 4500634709121, 0, 4500634709031, 0, 0, 0, 0, 0, 0, 0, 4500634603464, 0, 1533288642004, 0, 4500634602112, 0, 0, 0, 1533288668164, 0, 1533288669304, 0, 0, 0, 0, 0, 4425237538617, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4500634709031, 0, 4500634709031, 0, 0, 0, 0, 0, 4425237541123, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def x (z : Fin 3) (w : Word) : ℚ :=
  (massNumerator z w : ℚ) / 1000000000000000000000000000000000000000000000000000000000000
private def lower (z : Fin 3) (w : Word) : ℚ := -(lowerMagnitude z w : ℚ) / 1000000000000
private def upper (z : Fin 3) (w : Word) : ℚ := -(upperMagnitude z w : ℚ) / 1000000000000
private def bound (z : Fin 3) : ℚ := ((![0, 0, 29841607991] : Fin 3 → ℕ) z : ℚ) / 1000000000000

private theorem log_bounds (z : Fin 3) (w : Word)
    (hp : 0 < x z w / ∑ v, x z v) :
    (lower z w : ℝ) ≤ Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ∧
      Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ≤ (upper z w : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale z w) 16
  all_goals revert z w; decide +kernel

/-- A released outer boundary cell has a certified free-mode entropy and
letter-volume lower bound, with the actual global coarse weight included. -/
theorem solution
    (z : Fin 3) (hz : ((shape 29).val z).val = 0) :
    (denominator : ℝ) ^ 5 * (((![0, 0, 29841607991] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 0 (z + 1) (shapeEquiv 29) w : ℝ)) +
        (∑ w, (wordCounts 0 (z + 1) (shapeEquiv 29) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ z w, 0 ≤ x z w := by decide +kernel
  have hcert : ∀ z, bound z ≤
      (∑ w, x z w) * (-(∑ w, (x z w / ∑ v, x z v) * upper z w)) +
        (∑ w, x z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x z) (hx z) ones
    (lower z) (upper z) (log_bounds z) (bound z) (hcert z)
    ((denominator : ℝ) ^ 5) (by positivity)
  have hid : ∀ z : Fin 3, ((shape 29).val z).val = 0 → ∀ w : Word,
      (denominator : ℚ) ^ 5 * x z w = (alpha 0 29 * ((jointRows 0 29).map
        (fun a => if atom a.1 (z + 1) = w then a.2 else 0)).sum : ℕ) := by
    decide +kernel
  have he (w : Word) :
      (denominator : ℝ) ^ 5 * (x z w : ℝ) = (wordCounts 0 (z + 1) (shapeEquiv 29) w : ℝ) := by
    rw [mme_released_global_word_counts_row_marginal, Equiv.symm_apply_apply]
    have hh := congrArg (fun q : ℚ => (q : ℝ)) (hid z hz w)
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at hh
    exact hh
  simp_rw [he] at h
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
