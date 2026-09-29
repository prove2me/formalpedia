-- Prove2me | solution 1 for BerggrenHypercycleStars.factoring_star_search_cost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:37:31.949625+00:00
-- url     : https://prove2.me/submissions/d4775713-751f-47d7-99e9-24c14d381283

-- Sol generated from Cryptography/BerggrenStars/HypercycleStars.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Theorems.Thm_BerggrenHypercycleStars_card_spokeSet_ge

/-!
# The stars of the Berggren tree: hypercycle pencils in the Poincaré half-plane

This file explains, and proves exactly, the *visual* structure of the Berggren tree of
primitive Pythagorean triples embedded in the Poincaré upper half-plane `ℍ` by the Euclid
seed map

  `z(m, n) = (n + i) / m`,

namely the **families of straight lines that emanate from rational boundary points** and
which dominate any picture of the embedded tree.

## The phenomenon

Fix a boundary point `p/q ∈ ℚ ⊆ ∂ℍ` and an integer `k`. The seeds `(m, n)` with
`q * n - p * m = k` satisfy `Re z = p/q + (k/q) * Im z`, so they all lie on one Euclidean
half-line emanating from `p/q`. Such a Euclidean ray is *not* a geodesic: it is a
**hypercycle**, the curve of points at constant hyperbolic distance from the vertical
geodesic `(p/q, ∞)`. The main theorem `distVLine_hpoint` computes that distance exactly:

  `d_ℍ(z(m,n), geodesic at p/q) = arsinh (|q n - p m| / q)`.

So the picture is a superposition of *stars*: over each rational boundary point `p/q` sits
a discrete pencil of hypercycles indexed by `k ∈ ℤ`, at the quantized distances
`arsinh (|k| / q)`.

## Main results

* `isLeast_dist_vline`, `distVLine_eq` : for any `z ∈ ℍ` and any `a ∈ ℝ`, the distance from
  `z` to the complete geodesic `{Re = a}` is attained and equals `arsinh (|Re z - a| / Im z)`
  (a general half-plane fact, proved from `UpperHalfPlane.cosh_dist'`).
* `distVLine_hpoint` : the star formula above; `spoke_dist`, `costar_dist` : its two
  arithmetically meaningful specialisations, `arsinh n` at the boundary point `0` and
  `arsinh (m - n)` at the boundary point `1`.
* `charge_e1_eq`, `charge_e2_eq` : the two conserved *Lorentzian charges* of the Berggren
  action, `⟨v, e₁⟩ = -2n²` and `⟨v, e₂⟩ = -(m-n)²`, are exactly `-2 sinh²` and `-sinh²` of
  these two hyperbolic distances. The arithmetic invariants *are* geometric ones.
* `seedR_preserves_spoke`, `seedL_preserves_costar` : the Berggren move `B₃` slides a node
  along its `0`-hypercycle and `B₁` slides it along its `1`-hypercycle — each generator
  preserves one star exactly.
* `seedM_pell_flip`, `seedM_sinh_relation` : the third move `B₂` preserves no line of either
  star but negates the Pell form `m² - 2mn - n² = sinh²d₁ - 2 sinh²d₀`; this is the exact
  hyperbolic meaning of the Pell boundary layer.
* `spoke_tendsto_zero`, `costar_tendsto_one` : iterating `B₃` (resp. `B₁`) drives the node to
  the boundary point `0` (resp. `1`) *along* its hypercycle — the rays really do radiate out
  of the edge of the half-plane.
* `spoke_realized_iff` : an **exact census of the star**. The spoke index `n` occurs inside
  the hyperbolic ball `B(i, R)` if and only if `(n² + n + 1)/(n + 1) ≤ cosh R`; consequently
  the set of realized spoke indices is the initial interval `[1, K]` with
  `cosh R - 1 ≤ K < cosh R` (`spoke_realized_of_le`, `lt_cosh_of_spoke_realized`), so the
  number of visible rays in a ball of radius `R` is `Θ(e^R)`.
* `factoring_star_search_cost` : the cryptographic consequence. For odd `N` with two
  primitive representations, the nodes carrying `N` live in a ball of radius
  `R = ½ log N + log 2`, and the number of distinct hypercycles of the `0`-star meeting that
  ball is at least `√N / 2 - 1`: organising the collision search by star index costs `Θ(√N)`,
  the same as the naive enumeration.
* `dist_ge_spoke_gap` : colliding nodes, though at almost equal radius, are separated by at
  least the difference of their `arsinh` spoke indices, which is typically `≍ ½ log N`.

All of this is proved for Mathlib's genuine hyperbolic metric on `UpperHalfPlane`.
-/

open BerggrenHypercycleStars

open Real UpperHalfPlane

noncomputable section

/-! ## Part 0. Euclid seeds and the half-plane embedding

These mirror the definitions used elsewhere in the catalog for the Berggren tree. -/








/-! ## Part 1. The exact distance from a point to a vertical geodesic

The complete geodesics of `ℍ` with one endpoint at `∞` are the vertical lines `{Re = a}`.
We compute the distance from an arbitrary point to such a line, exactly, and show the
infimum is attained (at the *foot* of the perpendicular). -/
















/-! ## Part 2. The star over a rational boundary point

For a boundary point `p/q` and a seed `(m,n)`, the distance from `z(m,n)` to the geodesic
`(p/q, ∞)` depends only on the integer linear form `q n - p m`. -/




/-! ## Part 3. The Lorentzian charges are hyperbolic distances

The Berggren action preserves the Lorentz form `⟨v,w⟩ = v₁w₁ + v₂w₂ - v₃w₃` on the light cone
of Pythagorean triples, and the pairings with the two isotropic vectors `e₁ = (1,0,1)`,
`e₂ = (0,1,1)` are the standard conserved "charges". We identify them with the two stars. -/







/-! ## Part 4. Each Berggren generator slides along one star -/






/-! ## Part 5. The rays really do radiate out of the boundary -/


/-! ## Part 6. Exact census of the star, and the cost of a star-organised search -/











theorem sqrt_eq_exp_half_log {x : ℝ} (hx : 0 < x) : Real.sqrt x = Real.exp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf


/-! ## Part 7. The hyperbolic distance between colliding nodes *is* Euler's factoring datum

Euler's method factors `N` from two essentially different representations
`N = m₁² + n₁² = m₂² + n₂²` through the integer `G = m₁m₂ + n₁n₂`, whose gcd with `N` is a
proper divisor. We show that `G` is determined by the *hyperbolic distance* between the two
corresponding nodes: the arithmetic of the factorization is visible in the picture. -/






/-! ## Part 8. Motion along a ray: the steps shrink but the ray is infinitely long

Iterating `B₃` slides a node along one hypercycle of the `0`-star. The hyperbolic step length
of that motion is given by an exact formula and tends to `0`: the nodes crowd together as the
ray approaches the boundary point `0`. Nevertheless the ray has infinite hyperbolic length. -/






/-! ## Part 9. Separation: how close two nodes of the picture can be -/




/-! ## Part 10. Diophantine avoidance and the bookkeeping of the two star indices -/







open BerggrenHypercycleStars in
theorem solution(N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt N - 2 ≤ (spokeSet (Real.log N / 2 + Real.log 2)).card := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set R : ℝ := Real.log N / 2 + Real.log 2 with hRdef
  have hR : 0 ≤ R := by positivity
  have hexp : Real.exp R = 2 * Real.sqrt N := by
    rw [hRdef, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2),
      ← sqrt_eq_exp_half_log (by linarith : (0:ℝ) < (N:ℝ))]
    ring
  have hcosh : Real.sqrt N ≤ Real.cosh R := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-R)
    rw [hexp] at *
    linarith
  have := card_spokeSet_ge R hR
  linarith
