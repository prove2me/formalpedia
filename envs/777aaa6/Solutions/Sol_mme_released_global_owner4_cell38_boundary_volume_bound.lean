-- Prove2me | solution 1 for mme_released_global_owner4_cell38_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T05:26:16.297361+00:00
-- url     : https://prove2.me/submissions/ab393209-f466-4fa8-8fb0-a550701bb683

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
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52706549219916310668000000000000000000000000000000000000, 0, 0, 0, 0, 0, 46574782034161277844000000000000000000000000000000000000, 0, 46574782034161277844000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52706549215186630560000000000000000000000000000000000000, 0, 0, 0, 0, 0, 1036563936267605568696000000000000000000000000000000000000, 0, 1036563938566230101184000000000000000000000000000000000000, 0, 0, 0, 46574780984172293868000000000000000000000000000000000000, 0, 1036563960076815232368000000000000000000000000000000000000, 0, 46574780984172293868000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 46574782019972237520000000000000000000000000000000000000, 0, 46574781977405116548000000000000000000000000000000000000, 0, 0, 0, 46574780969983253544000000000000000000000000000000000000, 0, 1036563960015329390964000000000000000000000000000000000000, 0, 46574780984172293868000000000000000000000000000000000000, 0, 0, 0, 52706481315899000112000000000000000000000000000000000000, 0, 52706481334817720544000000000000000000000000000000000000, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def logScale (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def lowerMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4496873127307, 0, 0, 0, 0, 0, 4620553612168, 0, 4620553612168, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4496873127397, 0, 0, 0, 0, 0, 1517946234009, 0, 1517946231791, 0, 0, 0, 4620553634712, 0, 1517946211039, 0, 4620553634712, 0, 0, 0, 0, 0, 0, 0, 4620553612473, 0, 4620553613387, 0, 0, 0, 4620553635017, 0, 1517946211099, 0, 4620553634712, 0, 0, 0, 4496874415649, 0, 4496874415290, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def upperMagnitude (z : Fin 3) (w : Word) : ℕ :=
  ((![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4496873127306, 0, 0, 0, 0, 0, 4620553612167, 0, 4620553612167, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4496873127396, 0, 0, 0, 0, 0, 1517946234008, 0, 1517946231790, 0, 0, 0, 4620553634711, 0, 1517946211038, 0, 4620553634711, 0, 0, 0, 0, 0, 0, 0, 4620553612472, 0, 4620553613386, 0, 0, 0, 4620553635016, 0, 1517946211098, 0, 4620553634711, 0, 0, 0, 4496874415648, 0, 4496874415289, 0, 0, 0, 0, 0]] : Fin 3 → List ℕ) z).getD (wordIndex w) 0

private def x (z : Fin 3) (w : Word) : ℚ :=
  (massNumerator z w : ℚ) / 1000000000000000000000000000000000000000000000000000000000000
private def lower (z : Fin 3) (w : Word) : ℚ := -(lowerMagnitude z w : ℚ) / 1000000000000
private def upper (z : Fin 3) (w : Word) : ℚ := -(upperMagnitude z w : ℚ) / 1000000000000
private def bound (z : Fin 3) : ℚ := ((![0, 0, 29921870728] : Fin 3 → ℕ) z : ℚ) / 1000000000000

private theorem log_bounds (z : Fin 3) (w : Word)
    (hp : 0 < x z w / ∑ v, x z v) :
    (lower z w : ℝ) ≤ Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ∧
      Real.log ((x z w / ∑ v, x z v : ℚ) : ℝ) ≤ (upper z w : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale z w) 16
  all_goals revert z w; decide +kernel

/-- A released outer boundary cell has a certified free-mode entropy and
letter-volume lower bound, with the actual global coarse weight included. -/
theorem solution
    (z : Fin 3) (hz : ((shape 38).val z).val = 0) :
    (denominator : ℝ) ^ 5 * (((![0, 0, 29921870728] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 4 (z + 1) (shapeEquiv 38) w : ℝ)) +
        (∑ w, (wordCounts 4 (z + 1) (shapeEquiv 38) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  have hx : ∀ z w, 0 ≤ x z w := by decide +kernel
  have hcert : ∀ z, bound z ≤
      (∑ w, x z w) * (-(∑ w, (x z w / ∑ v, x z v) * upper z w)) +
        (∑ w, x z w * (ones w : ℚ)) * (1609437912434 / 1000000000000) := by
    decide +kernel
  have h := mme_rational_boundary_volume_certificate (x z) (hx z) ones
    (lower z) (upper z) (log_bounds z) (bound z) (hcert z)
    ((denominator : ℝ) ^ 5) (by positivity)
  have hid : ∀ z : Fin 3, ((shape 38).val z).val = 0 → ∀ w : Word,
      (denominator : ℚ) ^ 5 * x z w = (alpha 4 38 * ((jointRows 4 38).map
        (fun a => if atom a.1 (z + 1) = w then a.2 else 0)).sum : ℕ) := by
    decide +kernel
  have he (w : Word) :
      (denominator : ℝ) ^ 5 * (x z w : ℝ) = (wordCounts 4 (z + 1) (shapeEquiv 38) w : ℝ) := by
    rw [mme_released_global_word_counts_row_marginal, Equiv.symm_apply_apply]
    have hh := congrArg (fun q : ℚ => (q : ℝ)) (hid z hz w)
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at hh
    exact hh
  simp_rw [he] at h
  simpa only [bound, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
