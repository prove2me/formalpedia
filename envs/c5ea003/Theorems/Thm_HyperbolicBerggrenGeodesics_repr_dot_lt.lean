-- Prove2me | Theorems.Thm_HyperbolicBerggrenGeodesics_repr_dot_lt
-- name    : HyperbolicBerggrenGeodesics.repr_dot_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:23:50.78253+00:00
-- url     : https://prove2.me/theorems/05a2709e-bba1-4533-9988-e992477a4057
-- title:
--   One half of Euler's factorisation identity: `ac+bd < N` whenever `N = a²+b² = c²+d²`
-- statement:
--   One half of Euler's factorisation identity: `ac+bd < N` whenever `N = a²+b² = c²+d²`
--   and `ad ≠ bc`.
--
--   ```lean
--   theorem HyperbolicBerggrenGeodesics.repr_dot_lt{a b c d N : ℕ} (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N)
--       (hne : a * d ≠ b * c) : a * c + b * d < N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HyperbolicBerggrenGeodesics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HyperbolicBerggrenGeodesics.lean#L477

-- Thm stub generated from Geometry/HyperbolicBerggrenGeodesics.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics

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

theorem HyperbolicBerggrenGeodesics.repr_dot_lt{a b c d N : ℕ} (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N)
    (hne : a * d ≠ b * c) : a * c + b * d < N := by sorry
