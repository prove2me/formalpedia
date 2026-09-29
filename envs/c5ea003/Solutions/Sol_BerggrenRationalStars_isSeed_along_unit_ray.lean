-- Prove2me | solution 1 for BerggrenRationalStars.isSeed_along_unit_ray
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:46:52.404968+00:00
-- url     : https://prove2.me/submissions/6cb17f2a-b67e-4495-870c-e036eb19131e

-- Sol generated from Cryptography/BerggrenStars/RationalStarRays.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RationalStars
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

/-- Any common divisor of the coordinates of a node divides its star charge. Hence on the rays
of charge `±1` **all** lattice points are primitive. -/
theorem dvd_charge_of_common_divisor (p q m n : ℕ) {d : ℕ} (h1 : d ∣ m) (h2 : d ∣ n) :
    (d : ℤ) ∣ starCharge p q m n := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  refine ⟨(q : ℤ) * b - (p : ℤ) * a, ?_⟩
  simp only [starCharge]
  push_cast
  ring


/-! ## Part 3. Steps along a ray, and the ideal tip -/






open BerggrenRationalStars in
theorem solution(p q m n t : ℕ) (hpq : p < q) (h : IsSeed m n)
    (hk : starCharge p q m n = 1 ∨ starCharge p q m n = -1) :
    IsSeed (m + 2 * t * q) (n + 2 * t * p) := by
  have hpos := h.pos
  have hltmn := h.lt
  have hpar := h.parity
  have hpq2 : 2 * t * p ≤ 2 * t * q := Nat.mul_le_mul_left _ hpq.le
  refine ⟨by omega, by omega, ?_, ?_⟩
  · -- coprimality: a common divisor divides the charge `±1`
    have hd : (Nat.gcd (m + 2 * t * q) (n + 2 * t * p) : ℤ)
        ∣ starCharge p q (m + 2 * t * q) (n + 2 * t * p) :=
      dvd_charge_of_common_divisor p q _ _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    rw [starCharge_translate p q m n (2 * t)] at hd
    have : (Nat.gcd (m + 2 * t * q) (n + 2 * t * p) : ℤ) ∣ 1 := by
      rcases hk with hk | hk
      · rwa [hk] at hd
      · rw [hk] at hd; exact (dvd_neg.mp hd)
    have hle := Int.le_of_dvd (by norm_num) this
    have hg : Nat.gcd (m + 2 * t * q) (n + 2 * t * p) ≠ 0 := fun hzero => by
      have := (Nat.gcd_eq_zero_iff).mp hzero
      omega
    unfold Nat.Coprime
    omega
  · have hE : m + 2 * t * q + (n + 2 * t * p) = (m + n) + 2 * (t * q + t * p) := by ring
    rw [hE]
    omega
