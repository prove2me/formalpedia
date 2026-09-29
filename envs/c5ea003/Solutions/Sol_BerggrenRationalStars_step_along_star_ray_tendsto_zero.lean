-- Prove2me | solution 1 for BerggrenRationalStars.step_along_star_ray_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:46:55.188733+00:00
-- url     : https://prove2.me/submissions/1c0ec789-bff5-4058-98d0-244a7f4d2561

-- Sol generated from Cryptography/BerggrenStars/RationalStarRays.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RationalStars
import Theorems.Thm_BerggrenHypercycleStars_cosh_dist_hpoint_hpoint
import Theorems.Thm_BerggrenRationalStars_starCharge_translate

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


/-- **The exact hyperbolic step along a ray.** -/
theorem cosh_step_along_star_ray (p q m n t : ℕ) (hm : 0 < m) (hm' : 0 < m + t * q) :
    Real.cosh (dist (hpoint m n hm) (hpoint (m + t * q) (n + t * p) hm'))
      = (((t : ℝ) * (starCharge p q m n : ℝ)) ^ 2 + (m : ℝ) ^ 2 + ((m : ℝ) + t * q) ^ 2)
          / (2 * m * ((m : ℝ) + t * q)) := by
  rw [cosh_dist_hpoint_hpoint m n (m + t * q) (n + t * p) hm hm']
  have hcross : (n : ℝ) * ((m : ℝ) + t * q) - ((n : ℝ) + t * p) * m
      = (t : ℝ) * (starCharge p q m n : ℝ) := by
    rw [starCharge]; push_cast; ring
  push_cast
  rw [hcross]




open BerggrenRationalStars in
theorem solution(p q m n : ℕ) (hm : 0 < m) (hq : 0 < q) :
    Filter.Tendsto
      (fun j : ℕ => dist (hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega))
        (hpoint (m + 2 * j * q + 2 * q) (n + 2 * j * p + 2 * p) (by omega)))
      Filter.atTop (nhds 0) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set k : ℝ := (starCharge p q m n : ℝ) with hkdef
  set T : ℕ → ℝ := fun j =>
    (4 * k ^ 2 + 4 * (q : ℝ) ^ 2) /
      (2 * ((m : ℝ) + 2 * j * q) * (((m : ℝ) + 2 * j * q) + 2 * q)) with hT
  -- the exact step formula
  have hstep : ∀ j : ℕ,
      Real.cosh (dist (hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega))
        (hpoint (m + 2 * j * q + 2 * q) (n + 2 * j * p + 2 * p) (by omega))) = 1 + T j := by
    intro j
    have hM : (0 : ℝ) < (m : ℝ) + 2 * j * q := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    have hcharge : starCharge p q (m + 2 * j * q) (n + 2 * j * p) = starCharge p q m n :=
      starCharge_translate p q m n (2 * j)
    have hmain := cosh_step_along_star_ray p q (m + 2 * j * q) (n + 2 * j * p) 2
      (by omega) (by omega)
    rw [hcharge] at hmain
    have hcast : (((m + 2 * j * q : ℕ) : ℝ)) = (m : ℝ) + 2 * j * q := by push_cast; ring
    rw [hT]
    simp only
    rw [hmain, hcast, ← hkdef]
    field_simp
    ring
  -- `T j → 0`
  have hbd : ∀ j : ℕ, |T j| ≤ (4 * k ^ 2 + 4 * (q : ℝ) ^ 2) / (2 * j + 1) := by
    intro j
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hMj : (2 : ℝ) * j + 1 ≤ (m : ℝ) + 2 * j * q := by
      have : (2 : ℝ) * j * 1 ≤ 2 * j * q := by
        have hj : (0 : ℝ) ≤ 2 * j := by positivity
        nlinarith
      linarith
    have hMpos : (0 : ℝ) < (m : ℝ) + 2 * j * q := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hnum : (0 : ℝ) ≤ 4 * k ^ 2 + 4 * (q : ℝ) ^ 2 := by positivity
    rw [hT]
    simp only
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left hnum (by positivity)
    nlinarith
  have htend0 : Filter.Tendsto T Filter.atTop (nhds 0) := by
    have hlim : Filter.Tendsto
        (fun j : ℕ => (4 * k ^ 2 + 4 * (q : ℝ) ^ 2) / (2 * j + 1)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun j : ℕ => (2 : ℝ) * j + 1) Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_add_const_right
        apply Filter.Tendsto.const_mul_atTop (by norm_num)
        exact tendsto_natCast_atTop_atTop
      exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
    exact squeeze_zero_norm hbd hlim
  -- transfer to distances by monotonicity of `cosh`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcε : (1 : ℝ) < Real.cosh ε := (Real.one_lt_cosh (x := ε)).2 (ne_of_gt hε)
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 htend0) (Real.cosh ε - 1) (by linarith)
  refine ⟨K, fun j hj => ?_⟩
  have h1 : |T j - 0| < Real.cosh ε - 1 := hK j hj
  have h2 : Real.cosh (dist (hpoint (m + 2 * j * q) (n + 2 * j * p) (by omega))
      (hpoint (m + 2 * j * q + 2 * q) (n + 2 * j * p + 2 * p) (by omega))) < Real.cosh ε := by
    rw [hstep j]
    have := (abs_lt.1 h1).2
    linarith
  have h3 := Real.cosh_lt_cosh.1 h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  rwa [abs_of_nonneg dist_nonneg, abs_of_pos hε] at h3
