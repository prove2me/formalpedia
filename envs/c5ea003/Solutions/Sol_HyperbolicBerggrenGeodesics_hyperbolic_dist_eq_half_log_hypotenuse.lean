-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.hyperbolic_dist_eq_half_log_hypotenuse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:35:23.277166+00:00
-- url     : https://prove2.me/submissions/0cc986d2-4397-4b24-a73a-7efa3aee496f

-- Sol generated from Geometry/HyperbolicBerggrenGeodesics.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Theorems.Thm_HyperbolicBerggrenGeodesics_cosh_dist_hpoint_I
import Theorems.Thm_HyperbolicBerggrenGeodesics_log_cosh_sandwich

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







/-! ## Part 6. Non-vacuity: explicit witnesses -/








/-! ## Part 7. Second cycle: quantitative shape of a collision -/






open HyperbolicBerggrenGeodesics in
theorem solution{m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    |dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I -
        (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)| ≤ Real.log 2 := by
  set hm : 0 < m := lt_trans hn hnm with hmdef
  set d := dist (hpoint m n hm) UpperHalfPlane.I with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `m² ≥ n² + 1` because `n < m` are naturals
  have hsq : (n : ℝ) ^ 2 + 1 ≤ (m : ℝ) ^ 2 := by
    have : n ^ 2 + 1 ≤ m ^ 2 := by nlinarith [hnm, hn]
    exact_mod_cast this
  set c : ℝ := (m : ℝ) ^ 2 + (n : ℝ) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hc1 : 1 ≤ c := by nlinarith
  have hA : Real.cosh d = (c + 1) / (2 * m) := by
    rw [hd, cosh_dist_hpoint_I]
  set A : ℝ := (c + 1) / (2 * m) with hAdef
  have hApos : 0 < A := by positivity
  obtain ⟨hlow, hhigh⟩ := log_cosh_sandwich hd0
  rw [hA] at hlow hhigh
  -- Upper bound
  have hup : d ≤ Real.log 2 + (1 / 2) * Real.log c := by
    have key : (2 * A) ^ 2 ≤ 4 * c := by
      rw [hAdef]
      have h2m : c + 1 ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
      have : ((c + 1) / (m : ℝ)) ^ 2 ≤ 4 * c := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (c + 1), sq_nonneg ((m : ℝ))]
      calc (2 * ((c + 1) / (2 * (m : ℝ)))) ^ 2 = ((c + 1) / (m : ℝ)) ^ 2 := by
            field_simp
        _ ≤ 4 * c := this
    have h1 : Real.log (2 * A) ≤ Real.log (4 * c) := Real.log_le_log (by positivity) (by nlinarith)
    have h2 : 2 * Real.log (2 * A) = Real.log ((2 * A) ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    have h3 : Real.log ((2 * A) ^ 2) ≤ Real.log (4 * c) :=
      Real.log_le_log (by positivity) key
    have h4 : Real.log (4 * c) = 2 * Real.log 2 + Real.log c := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hcpos),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have : 2 * d ≤ 2 * Real.log 2 + Real.log c := by
      calc 2 * d ≤ 2 * Real.log (2 * A) := by linarith
        _ = Real.log ((2 * A) ^ 2) := h2
        _ ≤ Real.log (4 * c) := h3
        _ = 2 * Real.log 2 + Real.log c := h4
    linarith
  -- Lower bound
  have hlo : Real.log 2 + d ≥ (1 / 2) * Real.log c := by
    have hm2 : (m : ℝ) ^ 2 ≤ c := by nlinarith
    have key : c / 4 ≤ A ^ 2 := by
      rw [hAdef, div_pow, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - 1), mul_pos hcpos hcpos]
    have h2 : 2 * Real.log A = Real.log (A ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    have h3 : Real.log (c / 4) ≤ Real.log (A ^ 2) := Real.log_le_log (by positivity) key
    have h4 : Real.log (c / 4) = Real.log c - 2 * Real.log 2 := by
      rw [Real.log_div (ne_of_gt hcpos) (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have : Real.log c - 2 * Real.log 2 ≤ 2 * d := by
      calc Real.log c - 2 * Real.log 2 = Real.log (c / 4) := h4.symm
        _ ≤ Real.log (A ^ 2) := h3
        _ = 2 * Real.log A := h2.symm
        _ ≤ 2 * d := by linarith
    linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩
