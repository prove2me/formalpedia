-- Prove2me | Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
-- name    : Geometry_HyperbolicBerggrenGeodesics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:19:14.99917+00:00
-- url     : https://prove2.me/theorems/6c86289b-0fd9-4641-b4d1-305eac7b83b2
-- title:
--   Aether Catalog definitions — Geometry_HyperbolicBerggrenGeodesics
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HyperbolicBerggrenGeodesics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HyperbolicBerggrenGeodesics.lean by skeleton subtraction
import Mathlib

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

namespace HyperbolicBerggrenGeodesics

open Real

noncomputable section

/-! ## Part 1. Euclid seeds and the Berggren tree in seed coordinates -/

/-- A **Euclid seed** is a pair `(m, n)` of naturals with `0 < n < m`, coprime and of
opposite parity. Such pairs are in bijection with primitive Pythagorean triples via
`(m,n) ↦ (m² - n², 2mn, m² + n²)`. -/
structure IsSeed (m n : ℕ) : Prop where
  pos : 0 < n
  lt : n < m
  cop : Nat.Coprime m n
  parity : (m + n) % 2 = 1

/-- The three Berggren moves in Euclid-seed coordinates: `B₁`. -/
def seedL (p : ℕ × ℕ) : ℕ × ℕ := (2 * p.1 - p.2, p.1)

/-- The three Berggren moves in Euclid-seed coordinates: `B₂`. -/
def seedM (p : ℕ × ℕ) : ℕ × ℕ := (2 * p.1 + p.2, p.1)

/-- The three Berggren moves in Euclid-seed coordinates: `B₃`. -/
def seedR (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + 2 * p.2, p.2)

/-- Euclid's parametrisation of Pythagorean triples, over `ℤ`. -/
def euclidTriple (m n : ℤ) : ℤ × ℤ × ℤ := (m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)

/-- Berggren's matrix `B₁` acting on a triple. -/
def bStepL (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1 - 2 * t.2.1 + 2 * t.2.2, 2 * t.1 - t.2.1 + 2 * t.2.2, 2 * t.1 - 2 * t.2.1 + 3 * t.2.2)

/-- Berggren's matrix `B₂` acting on a triple. -/
def bStepM (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1 + 2 * t.2.1 + 2 * t.2.2, 2 * t.1 + t.2.1 + 2 * t.2.2, 2 * t.1 + 2 * t.2.1 + 3 * t.2.2)

/-- Berggren's matrix `B₃` acting on a triple. -/
def bStepR (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (-t.1 + 2 * t.2.1 + 2 * t.2.2, -2 * t.1 + t.2.1 + 2 * t.2.2, -2 * t.1 + 2 * t.2.1 + 3 * t.2.2)










/-! ## Part 2. The hyperbolic embedding and the logarithmic trajectory theorem -/

open UpperHalfPlane

/-- The Poincaré half-plane point attached to a Euclid seed `(m,n)`:
`z(m,n) = (n + i)/m = n/m + i/m`. The root seed `(2,1)` goes to `(1 + i)/2`. -/
def hpoint (m n : ℕ) (hm : 0 < m) : ℍ :=
  ⟨⟨(n : ℝ) / m, 1 / m⟩, by
    have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    show (0 : ℝ) < 1 / (m : ℝ)
    positivity⟩







/-! ## Part 3. The spine: combinatorial depth is *not* logarithmic -/

/-- The left spine of the Berggren tree, in seed coordinates: iterate `B₁` from the root. -/
def spine : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | k + 1 => seedL (spine k)




/-- The half-plane point of the depth-`k` spine node. -/
def spinePoint (k : ℕ) : ℍ := hpoint (k + 2) (k + 1) (by omega)






/-! ## Part 4. Geodesic energy -/

/-- Discrete length of a `k`-step trajectory in the hyperbolic plane. -/
def pathLength (z : ℕ → ℍ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, dist (z i) (z (i + 1))

/-- Discrete Dirichlet energy of a `k`-step trajectory in the hyperbolic plane. -/
def pathEnergy (z : ℕ → ℍ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, dist (z i) (z (i + 1)) ^ 2






/-! ## Part 5. From geometry to arithmetic: collisions factor the hypotenuse -/







/-! ## Part 6. Non-vacuity: explicit witnesses -/








/-! ## Part 7. Second cycle: quantitative shape of a collision -/




end

end HyperbolicBerggrenGeodesics


