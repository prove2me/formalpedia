-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.berggren_trajectory_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:38:30.259966+00:00
-- url     : https://prove2.me/submissions/1976bee1-b4f6-455a-b94d-5ab982df1c99

-- Sol generated from Geometry/HyperbolicBerggrenGeodesics.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Theorems.Thm_HyperbolicBerggrenGeodesics_hyperbolic_dist_eq_half_log_hypotenuse

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



theorem dist_le_pathLength (z : ℕ → ℍ) (k : ℕ) : dist (z 0) (z k) ≤ pathLength z k := by
  induction k with
  | zero => simp [pathLength]
  | succ k ih =>
    rw [pathLength, Finset.sum_range_succ, ← pathLength]
    exact le_trans (dist_triangle (z 0) (z k) (z (k + 1))) (by linarith)

/-- **Cauchy–Schwarz: length² ≤ (number of steps) · energy.** -/
theorem sq_pathLength_le (z : ℕ → ℍ) (k : ℕ) :
    pathLength z k ^ 2 ≤ (k : ℝ) * pathEnergy z k := by
  have := sq_sum_le_card_mul_sum_sq (s := Finset.range k)
    (f := fun i => dist (z i) (z (i + 1)))
  simpa [pathLength, pathEnergy] using this

/-- **Geodesic energy lower bound.** Any `k`-step trajectory joining two points at
hyperbolic distance `d` has discrete energy at least `d²/k`, with equality exactly for
uniformly-parametrised geodesics. -/
theorem geodesic_energy_lower_bound (z : ℕ → ℍ) (k : ℕ) (hk : 0 < k) :
    dist (z 0) (z k) ^ 2 / (k : ℝ) ≤ pathEnergy z k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : dist (z 0) (z k) ^ 2 ≤ pathLength z k ^ 2 := by
    have h0 : 0 ≤ dist (z 0) (z k) := dist_nonneg
    have := dist_le_pathLength z k
    nlinarith
  have h2 := sq_pathLength_le z k
  rw [div_le_iff₀ hkR]
  nlinarith



/-! ## Part 5. From geometry to arithmetic: collisions factor the hypotenuse -/







/-! ## Part 6. Non-vacuity: explicit witnesses -/








/-! ## Part 7. Second cycle: quantitative shape of a collision -/






open HyperbolicBerggrenGeodesics in
theorem solution{m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (z : ℕ → ℍ) (k : ℕ) (hk : 0 < k)
    (h0 : z 0 = UpperHalfPlane.I) (hkz : z k = hpoint m n (lt_trans hn hnm)) :
    ((1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2) ^ 2 / (k : ℝ)
      ≤ pathEnergy z k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hb := hyperbolic_dist_eq_half_log_hypotenuse hn hnm
  rw [abs_le] at hb
  -- the seed forces `m ≥ 2`, hence `c ≥ 5 > 4`, hence `½ log c ≥ log 2`
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc4 : (4 : ℝ) ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by nlinarith
  have hL : 0 ≤ (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2 := by
    have h1 : Real.log 4 ≤ Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) :=
      Real.log_le_log (by norm_num) hc4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hdist : (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2
      ≤ dist (z 0) (z k) := by
    rw [h0, hkz, dist_comm]
    linarith [hb.1]
  have hsq : ((1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2) ^ 2
      ≤ dist (z 0) (z k) ^ 2 := by nlinarith
  have := geodesic_energy_lower_bound z k hk
  calc ((1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2) ^ 2 / (k : ℝ)
      ≤ dist (z 0) (z k) ^ 2 / (k : ℝ) := by
        gcongr
    _ ≤ pathEnergy z k := this
