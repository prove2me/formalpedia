-- Prove2me | solution 1 for mme_released_global_owner3_cell2_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T05:03:25.447424+00:00
-- url     : https://prove2.me/submissions/4fc624fb-186e-4f02-8aac-63d96b2a5c01

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
  ((![[0, 0, 3968229347107034080000000000000000000000000000000000000, 0, 84994006317250972240000000000000000000000000000000000000, 0, 3968229348094903920000000000000000000000000000000000000, 0, 0, 0, 77017177367249103720000000000000000000000000000000000000, 0, 77017176917274391600000000000000000000000000000000000000, 0, 0, 0, 0, 0, 3968229344637359480000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77017177271919664160000000000000000000000000000000000000, 0, 77017176981485931200000000000000000000000000000000000000, 0, 0, 0, 0, 0, 84999287951002159240000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3968229153978480360000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def logScale (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def lowerMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 4824083780697, 0, 1759823027530, 0, 4824083780448, 0, 0, 0, 1858375287953, 0, 1858375293796, 0, 0, 0, 0, 0, 4824083781319, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1858375289191, 0, 1858375292962, 0, 0, 0, 0, 0, 1759760888211, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4824083829365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def upperMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 4824083780696, 0, 1759823027529, 0, 4824083780447, 0, 0, 0, 1858375287952, 0, 1858375293795, 0, 0, 0, 0, 0, 4824083781318, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1858375289190, 0, 1858375292961, 0, 0, 0, 0, 0, 1759760888210, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4824083829364, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def x (z : Fin 3) (w : Word) : ℚ :=
  (massNumerator z w : ℚ) / 1000000000000000000000000000000000000000000000000000000000000
private def lower (z : Fin 3) (w : Word) : ℚ := -(lowerMagnitude z w : ℚ) / 1000000000000
private def upper (z : Fin 3) (w : Word) : ℚ := -(upperMagnitude z w : ℚ) / 1000000000000
private def bound (z : Fin 3) : ℚ := ((![2487054614, 0, 0] : Fin 3 → ℕ) z : ℚ) / 1000000000000

private theorem log_bounds (z : Fin 3) (w : Word)
    (hp : 0 < x z w / ∑ v, x z v) :
    (lower z w : ℝ) ≤ Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ∧
      Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ≤ (upper z w : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale z w) 16
  all_goals revert z w; decide +kernel

/-- A released outer boundary cell has a certified free-mode entropy and
letter-volume lower bound, with the actual global coarse weight included. -/
theorem solution
    (z : Fin 3) (hz : ((shape 2).val z).val = 0) :
    (denominator : ℝ) ^ 5 * (((![2487054614, 0, 0] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 3 (z + 1) (shapeEquiv 2) w : ℝ)) +
        (∑ w, (wordCounts 3 (z + 1) (shapeEquiv 2) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ z w, 0 ≤ x z w := by decide +kernel
  have hcert : ∀ z, bound z ≤
      (∑ w, x z w) * (-(∑ w, (x z w / ∑ v, x z v) * upper z w)) +
        (∑ w, x z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x z) (hx z) ones
    (lower z) (upper z) (log_bounds z) (bound z) (hcert z)
    ((denominator : ℝ) ^ 5) (by positivity)
  have hid : ∀ z : Fin 3, ((shape 2).val z).val = 0 → ∀ w : Word,
      (denominator : ℚ) ^ 5 * x z w = (alpha 3 2 * ((jointRows 3 2).map
        (fun a => if atom a.1 (z + 1) = w then a.2 else 0)).sum : ℕ) := by
    decide +kernel
  have he (w : Word) :
      (denominator : ℝ) ^ 5 * (x z w : ℝ) = (wordCounts 3 (z + 1) (shapeEquiv 2) w : ℝ) := by
    rw [mme_released_global_word_counts_row_marginal, Equiv.symm_apply_apply]
    have hh := congrArg (fun q : ℚ => (q : ℝ)) (hid z hz w)
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at hh
    exact hh
  simp_rw [he] at h
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
