-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.semiprime_collision_splits_exactly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:09:09.429644+00:00
-- url     : https://prove2.me/submissions/8c47a2c8-0e1f-4647-97c7-00f726fecece

-- Sol generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_berggren_collision_splits

/-!
# Hyperbolic–Pythagorean Geodesics, cycle III: quadratic ball growth

The first cycle proved that the hyperbolic ball of radius `R` around `i` contains at least
`e^{R-2} - 1` Berggren nodes, and conjectured (sub-conjecture **C1-lite**) the true order
`e^{2R}`: the number of nodes should grow like the *hypotenuse*, not like its square root.

This file proves that conjecture.  The obstruction is arithmetic, not geometric: one has to
produce quadratically many *coprime* pairs of opposite parity, which requires a sieve.

## Main results

* `card_multiples_Ioc` : the exact count of multiples of `k` in an interval `(a, b]`.
* `sum_inv_sq_odd`, `sum_inv_odd` : two telescoping estimates,
  `∑_{i<n} 1/(2i+3)² ≤ 1/4` and `∑_{i<n} 1/(2i+3) ≤ √(2n+1) - 1`.
* `card_seedBox_lower` : **the sieve bound.**  For `K ≥ 256` the box
  `{m even, 2K < m ≤ 4K} × {n odd, 1 ≤ n ≤ 2K}` contains at least `K²/4` Euclid seeds.
* `hyperbolic_ball_quadratic_growth` : **C1-lite, closed.**  For every `K ≥ 256` the
  hyperbolic ball of radius `R = log K + 2` around the base point contains at least
  `e^{2R}/300` distinct Berggren nodes.  Since every node with hypotenuse `c` sits at
  distance `≈ ½ log c`, this is the true order of growth, and it shows definitively that
  geodesic search through the Berggren tree cannot beat exhaustive search: the ball that
  is guaranteed to contain a colliding pair for `N` already contains `≍ N` nodes.
-/

open HyperbolicBerggrenGeodesics

open Real UpperHalfPlane

noncomputable section

/-! ## Part A. Counting multiples -/



/-! ## Part B. Two telescoping estimates -/



/-! ## Part C. The sieve -/












/-! ## Part D. From the sieve to a quadratic lower bound -/



/-! ## Part E. Quadratic volume growth of hyperbolic balls (C1-lite, closed) -/





/-! ## Part F. Cycle IV: the matching upper bound, and exact semiprime splitting -/





open HyperbolicBerggrenGeodesics in
theorem solution{m₁ n₁ m₂ n₂ p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = p * q) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = p * q)
    (hne : (m₁, n₁) ≠ (m₂, n₂)) :
    (Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) = p ∧ Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) = q) ∨
      (Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) = q ∧ Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) = p) := by
  obtain ⟨hprod, hg1, hg2, hh1, hh2⟩ := berggren_collision_splits h₁ h₂ hN₁ hN₂ hne
  set g := Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) with hgdef
  set h := Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) with hhdef
  -- `g` is a divisor of `p q` other than `1` and `p q`, hence `p` or `q`
  have hgdvd : g ∣ p * q := Nat.gcd_dvd_left _ _
  have hgp : g = p ∨ g = q := by
    by_cases hdvd : p ∣ g
    · obtain ⟨t, ht⟩ := hdvd
      have htq : t ∣ q := by
        have : p * t ∣ p * q := ht ▸ hgdvd
        exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.pos.ne' : (p : ℕ) ≠ 0)).1 this
      rcases (hq.eq_one_or_self_of_dvd t htq) with h1 | h1
      · left; rw [ht, h1, mul_one]
      · exfalso; rw [ht, h1] at hg2; omega
    · right
      have hcopg : Nat.Coprime g p := (Nat.Prime.coprime_iff_not_dvd hp).2 hdvd |>.symm
      have : g ∣ q := hcopg.dvd_of_dvd_mul_left hgdvd
      rcases (hq.eq_one_or_self_of_dvd g this) with h1 | h1
      · exact absurd h1 (by omega)
      · exact h1
  have hqpos : 0 < q := hq.pos
  have hppos : 0 < p := hp.pos
  rcases hgp with hgval | hgval
  · left
    refine ⟨hgval, ?_⟩
    rw [hgval] at hprod
    exact Nat.eq_of_mul_eq_mul_left hppos hprod
  · right
    refine ⟨hgval, ?_⟩
    rw [hgval, mul_comm p q] at hprod
    exact Nat.eq_of_mul_eq_mul_left hqpos hprod
