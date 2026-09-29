-- Prove2me | solution 1 for SpacetimeDonuts.geo_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:55:55.870815+00:00
-- url     : https://prove2.me/submissions/8da819b9-7566-4bc6-b919-41539724694f

-- Sol generated from Shared/SpacetimeDonuts.lean
import Mathlib
import Definitions.Def_Shared_SpacetimeDonuts

/-!
# Spacetime Donuts: geodesics and the wrapping lattice of the flat 3-torus

This file develops, entirely inside `Mathlib`'s `AddCircle` machinery, a rigorous
account of the *flat three-torus* `𝕋³ = (ℝ/ℤ)³` viewed as a model of a
spatially closed ("donut-shaped") universe.

The three-torus is the quotient of `ℝ³` by the integer translation lattice.
Two intertwined structures make the "donut universe" precise:

* **Closed geodesics.** Straight lines in the universal cover `ℝ³` project to
  geodesics of the flat metric. A line in an *integer* direction `n ∈ ℤ³`
  projects to a *closed* geodesic: it returns to its starting point after unit
  time. Every nonzero integer direction produces a genuinely nonconstant loop,
  so the universe is threaded by closed geodesics that wrap around it.

* **The wrapping lattice.** The kernel of the covering projection
  `proj : ℝ³ → 𝕋³` is exactly the integer lattice `ℤ³`, the group of covering
  translations. Under the standard covering-space dictionary this group *is* the
  fundamental group of the torus, so `π₁(𝕋³) ≅ ℤ³`. The three standard basis
  vectors are linearly independent, giving the *three independent families* of
  ways to wrap around the universe.

## Main results

* `geo_periodic` : an integer-direction geodesic has period one (it is closed).
* `geo_nontrivial` : a nonzero integer direction gives a nonconstant loop.
* `geo_eq_proj_line` : each such geodesic is the projection of a straight line.
* `mem_ker_iff` : the kernel of the covering projection is the integer lattice.
* `ker_proj_eq_range` : the covering-translation group equals the image of `ℤ³`.
* `latt_injective` : the wrapping lattice is a faithful copy of `ℤ³`.
* `standard_basis_indep` : the three fundamental wrapping directions are
  independent — three independent families of loops.
* `geo_class` : the free-homotopy class (endpoint of the canonical lift) of an
  integer geodesic is its direction vector, and this assignment is injective,
  so the torus carries infinitely many distinct closed geodesics.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): If the universe is a flat 3-torus then it must
contain closed spatial geodesics, and these organize into exactly three
independent families indexed by the generators of `π₁ = ℤ³`.

Experiment (Experimenter): Model `𝕋³` as `Fin 3 → AddCircle 1`. Realize
geodesics as projections of straight lines `t ↦ t·n`. Compute the covering
kernel and identify it with the integer lattice.

Analysis (Analyst): The "period one" property is exactly the statement that
the direction is an integer vector; nonconstancy is witnessed by the half-way
point `t = 1/(2 nᵢ)` landing on the order-two element `1/2 ∈ ℝ/ℤ`. The kernel
computation is the covering-space incarnation of `π₁(𝕋³) ≅ ℤ³`.

Critique (Critic): Nonconstancy must be proved, not assumed — a constant loop
is still "periodic". We prove genuine nonconstancy from `n ≠ 0`. The claim
`π₁ ≅ ℤ³` is rendered honestly as the covering-translation group (`ker proj`)
being a free `ℤ`-module of rank three, avoiding any appeal to unformalized
topology.

Synthesis (PI): Closed geodesics + a rank-three faithful lattice together give
the "three independent families of wrapping", the concrete content of Rucker's
donut-shaped spacetime.
-/

open AddCircle

open SpacetimeDonuts







/-- The geodesic starts at the base point of the torus. -/
@[simp] theorem geo_zero (n : Fin 3 → ℤ) : geo n 0 = 0 := by
  funext i
  show (((0 : ℝ) * n i : ℝ) : AddCircle (1 : ℝ)) = 0
  simp


/-! ## The wrapping lattice and `π₁(𝕋³) ≅ ℤ³` -/







/-! ## Homotopy classes of closed geodesics -/





open SpacetimeDonuts in
theorem solution(n : Fin 3 → ℤ) (hn : n ≠ 0) : ∃ t : ℝ, geo n t ≠ geo n 0 := by
  rw [Function.ne_iff] at hn
  obtain ⟨i, hi⟩ := hn
  refine ⟨1 / (2 * n i), ?_⟩
  intro h
  have hne : (n i : ℝ) ≠ 0 := by exact_mod_cast (by simpa using hi)
  have hci := congrFun h i
  rw [geo_zero] at hci
  simp only [geo, Pi.zero_apply] at hci
  rw [show (1 / (2 * (n i : ℝ)) * n i : ℝ) = 1 / 2 by field_simp] at hci
  rw [AddCircle.coe_eq_zero_iff] at hci
  obtain ⟨m, hm⟩ := hci
  simp only [zsmul_eq_mul, mul_one] at hm
  have h1 : (2 * m : ℤ) = 1 := by
    have h2 : (2 : ℝ) * m = 1 := by rw [hm]; ring
    exact_mod_cast h2
  omega
