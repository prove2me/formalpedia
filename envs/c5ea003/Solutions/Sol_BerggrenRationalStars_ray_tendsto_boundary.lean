-- Prove2me | solution 1 for BerggrenRationalStars.ray_tendsto_boundary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:46:53.697191+00:00
-- url     : https://prove2.me/submissions/6421fc98-c829-4a05-ad86-884611331b8e

-- Sol generated from Cryptography/BerggrenStars/RationalStarRays.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RationalStars

/-!
# The individual rays of a rational star: straight lines, shrinking steps, ideal tips

`Cryptography.BerggrenStars.RationalStars` determines *which* rays of the pencil over a
boundary rational `p/q` are populated by Berggren nodes. This file studies a single ray.

Fix a boundary rational `p/q` and a star charge `k = q n - p m`. The nodes of charge `k` are
exactly the lattice translates `(m + t q, n + t p)` of one another, and here we prove that they
form the visible radial line of the picture:

## Main results

* `star_ray_line` : the exact Euclidean equation of the ray,
  `Re z = p/q + (k/q) · Im z`. Charge `k` is the Euclidean line parameter.
* `ray_constant_distVLine` : two nodes of equal charge are at equal hyperbolic distance from
  the geodesic over `p/q` — the ray is a hypercycle, not a geodesic.
* `dvd_charge_of_common_divisor`, `isSeed_along_unit_ray` : the arithmetic of a ray. Any common
  divisor of the two coordinates of a node divides its charge; consequently the two **unit
  rays** `k = ±1` of every rational star are *fully* populated — every second lattice point on
  them is a Berggren node. These are the brightest lines of the star.
* `cross_along_ray` : the seed cross product of two nodes on a ray of charge `k` at lattice
  distance `t` is exactly `t k`; the charge is the symplectic area form of the ray.
* `cosh_step_along_star_ray` : hence the exact hyperbolic step length along the ray,
  `cosh(step) = ((tk)² + m² + m'²)/(2 m m')`.
* `step_along_star_ray_tendsto_zero` : the steps along a ray tend to `0`. A ray is an infinite
  path of shrinking steps — the reason it renders as a smooth straight line rather than as a
  sequence of separated dots.
* `ray_tendsto_boundary` : the ray converges to its ideal tip `p/q`. Every rational boundary
  point is the limit of the ray(s) of its own star.
-/

open BerggrenRationalStars

open BerggrenHypercycleStars Real UpperHalfPlane

/-! ## Part 1. The ray is a Euclidean straight line through `p/q`, and a hypercycle -/



/-! ## Part 2. The arithmetic of a ray: the unit rays are fully populated -/



/-! ## Part 3. Steps along a ray, and the ideal tip -/






open BerggrenRationalStars in
theorem solution(p q m n : ℕ) (hm : 0 < m) (hq : 0 < q) :
    Filter.Tendsto
      (fun j : ℕ => ((hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega) : ℍ) : ℂ))
      Filter.atTop (nhds ((((p : ℝ) / (q : ℝ) : ℝ)) : ℂ)) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hQ : (0 : ℝ) < (q : ℝ) := by linarith
  set k : ℝ := |(starCharge p q m n : ℝ)| with hk
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ j : ℕ,
      ‖((hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega) : ℍ) : ℂ)
          - ((((p : ℝ) / (q : ℝ) : ℝ)) : ℂ)‖ ≤ (k / q + 1) / (2 * j + 1) := by
    intro j
    have hMj : (2 : ℝ) * j + 1 ≤ ((m + 2 * j * q : ℕ) : ℝ) := by
      push_cast
      have hj : (0 : ℝ) ≤ 2 * j := by positivity
      nlinarith
    have hMpos : (0 : ℝ) < ((m + 2 * j * q : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
      push_cast
      nlinarith
    -- real and imaginary parts (both `rfl` for the half-plane embedding)
    have hre : (((hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega) : ℍ) : ℂ)
        - ((((p : ℝ) / (q : ℝ) : ℝ)) : ℂ)).re
        = ((n + 2 * j * p : ℕ) : ℝ) / ((m + 2 * j * q : ℕ) : ℝ) - (p : ℝ) / q := rfl
    have him : (((hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega) : ℍ) : ℂ)
        - ((((p : ℝ) / (q : ℝ) : ℝ)) : ℂ)).im = 1 / ((m + 2 * j * q : ℕ) : ℝ) := by
      show 1 / ((m + 2 * j * q : ℕ) : ℝ) - 0 = _
      ring
    have hrev : ((n + 2 * j * p : ℕ) : ℝ) / ((m + 2 * j * q : ℕ) : ℝ) - (p : ℝ) / q
        = (starCharge p q m n : ℝ) / (q * ((m + 2 * j * q : ℕ) : ℝ)) := by
      rw [starCharge]
      push_cast
      field_simp
      ring
    calc ‖((hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega) : ℍ) : ℂ)
            - ((((p : ℝ) / (q : ℝ) : ℝ)) : ℂ)‖
        ≤ |(((hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega) : ℍ) : ℂ)
              - ((((p : ℝ) / (q : ℝ) : ℝ)) : ℂ)).re|
          + |(((hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega) : ℍ) : ℂ)
              - ((((p : ℝ) / (q : ℝ) : ℝ)) : ℂ)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = (k / q + 1) / ((m + 2 * j * q : ℕ) : ℝ) := by
          rw [hre, him, hrev, abs_div,
            abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) * ((m + 2 * j * q : ℕ) : ℝ)),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((m + 2 * j * q : ℕ) : ℝ)), ← hk]
          field_simp
      _ ≤ (k / q + 1) / (2 * j + 1) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hMj
  have hlim : Filter.Tendsto (fun j : ℕ => (k / q + 1) / (2 * j + 1)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun j : ℕ => (2 : ℝ) * j + 1) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_add_const_right
      apply Filter.Tendsto.const_mul_atTop (by norm_num)
      exact tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
  exact squeeze_zero (fun j => norm_nonneg _) hbd hlim
