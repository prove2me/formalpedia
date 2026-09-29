-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.berggren_collision_factors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:31:07.371423+00:00
-- url     : https://prove2.me/submissions/da05ff81-07c1-4a1b-a392-70e6c989ad17

-- Sol generated from Geometry/HyperbolicBerggrenGeodesics.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Theorems.Thm_HyperbolicBerggrenGeodesics_euler_two_representations_factor

/-!
# Hyperbolic–Pythagorean Geodesics: the Berggren tree in the Poincaré half-plane

This file develops a rigorous bridge between three a-priori unrelated objects:

* the **Berggren ternary tree** of primitive Pythagorean triples (combinatorics /
  arithmetic),
* the **hyperbolic plane** in the Poincaré upper half-plane model `ℍ`
  (Riemannian geometry), and
* **integer factorization** via Euler's two-representation method (number theory).

## Main results

* `bStepL_triple`, `bStepM_triple`, `bStepR_triple` : the three Berggren matrices
  `B₁, B₂, B₃` acting on Pythagorean triples are conjugate, through the Euclid
  parametrisation `(m,n) ↦ (m²-n², 2mn, m²+n²)`, to the three linear maps
  `(m,n) ↦ (2m-n, m), (2m+n, m), (m+2n, n)` on Euclid seeds.
* `seed_step*_isSeed` : the three seed maps preserve the "primitive seed" conditions
  (`0 < n < m`, `gcd m n = 1`, opposite parity).
* `cosh_dist_hpoint_I` : the exact hyperbolic cosine of the distance from the base
  point `i` to the node point `z(m,n) = (n + i)/m`, namely `(m² + n² + 1)/(2m)`.
* `hyperbolic_dist_eq_half_log_hypotenuse` : **the logarithmic trajectory theorem.**
  For every Euclid seed with hypotenuse `c = m² + n²`,
  `|d_ℍ(i, z(m,n)) - ½ log c| ≤ log 2`.
  So *every* node of the Berggren tree, no matter how deep, sits at hyperbolic
  distance `½ log c + O(1)` from the root: the geodesic trajectory is
  logarithmic — sub-linear — in the size of the triple.
* `combDepth_hypotenuse` and `no_logarithmic_depth_bound` : by contrast the
  *combinatorial* depth is **not** logarithmic. The spine `(2,1) → (3,2) → (4,3) → …`
  has depth `k` and hypotenuse only `2k² + 6k + 5`, so depth is `Θ(√c)` there.
  Hence the hyperbolic metric compresses the tree exponentially.
* `hyperbolic_ball_volume_growth` : a **no-free-lunch** theorem. The number of
  Berggren nodes inside the hyperbolic ball of radius `R` around `i` grows like
  `e^{R}`, i.e. like the hypotenuse itself. A short geodesic does not make the
  search cheap.
* `geodesic_energy_lower_bound` : the Cauchy–Schwarz bound `E ≥ d²/k` relating the
  discrete energy of a `k`-step trajectory to the hyperbolic displacement, and
  `berggren_path_energy_lower_bound`, its specialisation to Berggren paths.
* `euler_two_representations_factor` : two essentially distinct representations
  `N = a² + b² = c² + d²` produce a **non-trivial divisor** `gcd(N, ac+bd)` of `N`.
* `berggren_collision_factors` : two distinct Berggren nodes sharing a hypotenuse
  `N` factor `N`.

## Design notes

Distances are Mathlib's genuine hyperbolic metric on `UpperHalfPlane` (`ℍ`), not a
hand-rolled surrogate; `UpperHalfPlane.cosh_dist'` is the only geometric input.
-/

open HyperbolicBerggrenGeodesics

open Real

noncomputable section

/-! ## Part 1. Euclid seeds and the Berggren tree in seed coordinates -/


















/-! ## Part 2. The hyperbolic embedding and the logarithmic trajectory theorem -/

open UpperHalfPlane








/-! ## Part 3. The spine: combinatorial depth is *not* logarithmic -/











/-! ## Part 4. Geodesic energy -/








/-! ## Part 5. From geometry to arithmetic: collisions factor the hypotenuse -/




/-- Two distinct coprime seeds cannot be proportional. -/
theorem seed_cross_ne {m₁ n₁ m₂ n₂ : ℕ} (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hne : (m₁, n₁) ≠ (m₂, n₂)) : m₁ * n₂ ≠ n₁ * m₂ := by
  intro hcross
  have hm1 : 0 < m₁ := lt_trans h₁.pos h₁.lt
  have hd1 : m₁ ∣ m₂ := h₁.cop.dvd_of_dvd_mul_left ⟨n₂, hcross.symm⟩
  have hd2 : m₂ ∣ m₁ :=
    h₂.cop.dvd_of_dvd_mul_left ⟨n₁, by rw [mul_comm n₂ m₁, hcross]; exact mul_comm n₁ m₂⟩
  have hm : m₁ = m₂ := Nat.dvd_antisymm hd1 hd2
  subst hm
  have : n₂ = n₁ :=
    Nat.eq_of_mul_eq_mul_left hm1 (by rw [hcross]; exact mul_comm n₁ m₁)
  exact hne (by simp [this])



/-! ## Part 6. Non-vacuity: explicit witnesses -/








/-! ## Part 7. Second cycle: quantitative shape of a collision -/






open HyperbolicBerggrenGeodesics in
theorem solution{m₁ n₁ m₂ n₂ N : ℕ} (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = N) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = N) (hne : (m₁, n₁) ≠ (m₂, n₂)) :
    1 < Nat.gcd N (m₁ * m₂ + n₁ * n₂) ∧ Nat.gcd N (m₁ * m₂ + n₁ * n₂) < N := by
  have hm1 : 0 < m₁ := lt_trans h₁.pos h₁.lt
  have hm2 : 0 < m₂ := lt_trans h₂.pos h₂.lt
  refine euler_two_representations_factor hm1 hm2 h₂.pos hN₁ hN₂ ?_ ?_
  · exact seed_cross_ne h₁ h₂ hne
  · -- `m₁ m₂ > n₁ n₂` because `m > n` in both seeds
    have hlt : n₁ * n₂ < m₁ * m₂ :=
      Nat.mul_lt_mul_of_lt_of_le h₁.lt h₂.lt.le (lt_trans h₂.pos h₂.lt)
    omega
