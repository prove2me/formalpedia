-- Prove2me | solution 1 for mme_released_global_owner0_cell6_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T04:09:19.865135+00:00
-- url     : https://prove2.me/submissions/12f46500-c499-4961-b37a-1e75c557e2fe

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
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2946463630044043545000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71596046923566475538000000000000000000000000000000000000, 0, 0, 0, 0, 0, 86329761127603832119000000000000000000000000000000000000, 0, 86329761117096472606000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2946463522969046603000000000000000000000000000000000000, 0, 0, 0, 0, 0, 86329761124601729401000000000000000000000000000000000000, 0, 86329761085574394067000000000000000000000000000000000000, 0, 0, 0, 2948232314357199168000000000000000000000000000000000000, 0, 71645969802303323810000000000000000000000000000000000000, 0, 2948232351883483143000000000000000000000000000000000000, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def logScale (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 8, 0, 3, 0, 8, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def lowerMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5134703077127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1944268897025, 0, 0, 0, 0, 0, 1757134363628, 0, 1757134363749, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5134703113467, 0, 0, 0, 0, 0, 1757134363663, 0, 1757134364115, 0, 0, 0, 5134102983625, 0, 1943571854608, 0, 5134102970896, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def upperMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5134703077126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1944268897024, 0, 0, 0, 0, 0, 1757134363627, 0, 1757134363748, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5134703113466, 0, 0, 0, 0, 0, 1757134363662, 0, 1757134364114, 0, 0, 0, 5134102983624, 0, 1943571854607, 0, 5134102970895, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def x (z : Fin 3) (w : Word) : ℚ :=
  (massNumerator z w : ℚ) / 1000000000000000000000000000000000000000000000000000000000000
private def lower (z : Fin 3) (w : Word) : ℚ := -(lowerMagnitude z w : ℚ) / 1000000000000
private def upper (z : Fin 3) (w : Word) : ℚ := -(upperMagnitude z w : ℚ) / 1000000000000
private def bound (z : Fin 3) : ℚ := ((![2518371893, 0, 0] : Fin 3 → ℕ) z : ℚ) / 1000000000000

private theorem log_bounds (z : Fin 3) (w : Word)
    (hp : 0 < x z w / ∑ v, x z v) :
    (lower z w : ℝ) ≤ Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ∧
      Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ≤ (upper z w : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale z w) 16
  all_goals revert z w; decide +kernel

/-- A released outer boundary cell has a certified free-mode entropy and
letter-volume lower bound, with the actual global coarse weight included. -/
theorem solution
    (z : Fin 3) (hz : ((shape 6).val z).val = 0) :
    (denominator : ℝ) ^ 5 * (((![2518371893, 0, 0] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 0 (z + 1) (shapeEquiv 6) w : ℝ)) +
        (∑ w, (wordCounts 0 (z + 1) (shapeEquiv 6) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ z w, 0 ≤ x z w := by decide +kernel
  have hcert : ∀ z, bound z ≤
      (∑ w, x z w) * (-(∑ w, (x z w / ∑ v, x z v) * upper z w)) +
        (∑ w, x z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x z) (hx z) ones
    (lower z) (upper z) (log_bounds z) (bound z) (hcert z)
    ((denominator : ℝ) ^ 5) (by positivity)
  have hid : ∀ z : Fin 3, ((shape 6).val z).val = 0 → ∀ w : Word,
      (denominator : ℚ) ^ 5 * x z w = (alpha 0 6 * ((jointRows 0 6).map
        (fun a => if atom a.1 (z + 1) = w then a.2 else 0)).sum : ℕ) := by
    decide +kernel
  have he (w : Word) :
      (denominator : ℝ) ^ 5 * (x z w : ℝ) = (wordCounts 0 (z + 1) (shapeEquiv 6) w : ℝ) := by
    rw [mme_released_global_word_counts_row_marginal, Equiv.symm_apply_apply]
    have hh := congrArg (fun q : ℚ => (q : ℝ)) (hid z hz w)
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at hh
    exact hh
  simp_rw [he] at h
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
