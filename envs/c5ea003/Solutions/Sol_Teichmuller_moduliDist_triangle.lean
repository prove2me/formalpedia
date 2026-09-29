-- Prove2me | solution 1 for Teichmuller.moduliDist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:37:43.562686+00:00
-- url     : https://prove2.me/submissions/4efea1de-293e-4127-a31e-871f66adba8e

-- Sol generated from Geometry/Teichmuller/ModuliSpace.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_ModuliSpace
import Definitions.Def_Geometry_Teichmuller_TorusSpace
import Definitions.Def_Geometry_Teichmuller_TranslationLength
import Theorems.Thm_Teichmuller_moduliDist_le
import Theorems.Thm_Teichmuller_teichDist_eq_half_dist
import Theorems.Thm_Teichmuller_teichDist_triangle
/-
# The mapping class group, the moduli space of tori, and its degeneracies

The mapping class group of the torus is `SL(2, ℤ)`, acting on the Teichmüller space `ℍ` of
marked tori by change of marking, i.e. by Möbius transformations.  The moduli space of tori is
the quotient `ℍ / SL(2, ℤ)`, whose (pseudo-)distance is

    d_M (τ, τ') = inf over the mapping class group of d_T (τ, g · τ') .

This file proves:

* `Teichmuller.teichDist_smul` : **the mapping class group acts by isometries** of the
  Teichmüller metric — the property that makes the moduli distance well defined;
* `Teichmuller.moduliDist_comm`, `moduliDist_triangle`, `moduliDist_nonneg`,
  `moduliDist_smul_left`, `moduliDist_smul_right` : the moduli distance is a
  mapping-class-group-invariant pseudometric on `ℍ`, i.e. a genuine distance on the quotient;
* `Teichmuller.moduliDist_self_smul` and `Teichmuller.exists_ne_moduliDist_eq_zero` :
  the moduli distance is *only* a pseudometric on `ℍ`: distinct marked tori can be
  isomorphic as unmarked tori — the quotient is nontrivial;
* `Teichmuller.exists_nontrivial_stabilizer` : **the action is not free**: the square root of
  `-1` in `SL(2, ℤ)` fixes the square torus `i` and is nontrivial even modulo `±1`; hence the
  moduli space is an orbifold, not a manifold, and the quotient map is not a covering;
* `Teichmuller.exists_order_three_stabilizer` and `Teichmuller.smul_rho_ne_I` : the hexagonal
  torus `ρ = -1/2 + i√3/2` carries a stabiliser of order **three** in `PSL(2, ℤ)`, and
  `Teichmuller.sq_eq_one_of_smul_I_eq` shows the stabiliser of `i` has order **two**; hence the
  two cone points lie in different orbits and the moduli space has at least two distinct
  orbifold singularities, of cone angles `π` and `2π/3`;
* `Teichmuller.teichDist_T_pos` together with `Teichmuller.exists_teichDist_T_lt` :
  the parabolic mapping class `T : τ ↦ τ + 1` has **zero translation length which is not
  attained** — the quantitative source of the noncompactness of the moduli space
  (its "cusp"), in sharp contrast with the Anosov classes of
  `Geometry.Teichmuller.TranslationLength`, whose translation length is positive and attained.

-- !-- Lab Notes -- !--
Hypothesizer: the three Nielsen–Thurston types (elliptic / parabolic / Anosov) should be
*visible in the metric* on Teichmüller space: fixed point, infimum-zero-not-attained, and
positive-attained respectively.
Experimenter: the displacement identity `cosh_dist_smul` computes all three at once.  For
`S = !![0,-1;1,0]` (trace `0`) the displacement vanishes at `i`; for `T = !![1,1;0,1]`
(trace `2`) it equals `arcosh (1 + 1/(2y²)) > 0`, tending to `0` as `y → ∞`; for trace `> 2`
it is bounded below by `arcosh ((t²-2)/2) > 0`.  Analyst: the three cases are exactly
`|tr| < 2`, `= 2`, `> 2` — the metric geometry of the moduli space is governed by the trace,
and the failure of properness at the cusp is the parabolic case.
Critic: "the action is not free" is weaker than "the orbifold has two distinct cone points" —
the latter needs the stabiliser of `i` computed exactly.  Experimenter: solving `g · i = i`
over `ℤ` forces `a = d`, `b = -c`, hence `a² + c² = det g = 1`, whose only integral solutions
are the four points `(±1, 0), (0, ±1)`; all four square to `±1`.  Conjugating the order-three
stabiliser of `ρ` into the stabiliser of `i` therefore yields a contradiction, so the two cone
points are distinct in moduli.
-/

open Teichmuller

open Complex UpperHalfPlane Matrix MatrixGroups

variable (τ τ' τ'' : ℍ)

/-- The `SL(2, ℤ)`-action on `ℍ` is the restriction of the `SL(2, ℝ)`-action. -/
theorem int_smul_eq (g : SL(2, ℤ)) (z : ℍ) :
    g • z = (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- The mapping class group acts by isometries of the hyperbolic metric. -/
theorem dist_int_smul (g : SL(2, ℤ)) (z w : ℍ) : dist (g • z) (g • w) = dist z w := by
  rw [int_smul_eq g z, int_smul_eq g w]
  exact dist_smul _ _ _

/-- **The mapping class group acts by isometries of the Teichmüller metric.** -/
theorem teichDist_smul (g : SL(2, ℤ)) : teichDist (g • τ) (g • τ') = teichDist τ τ' := by
  rw [teichDist_eq_half_dist, teichDist_eq_half_dist, dist_int_smul]



























open Teichmuller in
theorem solution: moduliDist τ τ'' ≤ moduliDist τ τ' + moduliDist τ' τ'' := by
  have step : ∀ g h : SL(2, ℤ),
      moduliDist τ τ'' ≤ teichDist τ (g • τ') + teichDist τ' (h • τ'') := by
    intro g h
    have h1 : teichDist τ ((g * h) • τ'') ≤ teichDist τ (g • τ') + teichDist (g • τ') ((g * h) • τ'')
      := teichDist_triangle τ (g • τ') ((g * h) • τ'')
    have h2 : teichDist (g • τ') ((g * h) • τ'') = teichDist τ' (h • τ'') := by
      rw [SemigroupAction.mul_smul, teichDist_smul]
    calc moduliDist τ τ'' ≤ teichDist τ ((g * h) • τ'') := moduliDist_le _ _ _
      _ ≤ teichDist τ (g • τ') + teichDist τ' (h • τ'') := by rw [h2] at h1; exact h1
  have step2 : ∀ g : SL(2, ℤ),
      moduliDist τ τ'' - teichDist τ (g • τ') ≤ moduliDist τ' τ'' := by
    intro g
    refine le_ciInf fun h => ?_
    have := step g h
    linarith
  have step3 : ∀ g : SL(2, ℤ),
      moduliDist τ τ'' - moduliDist τ' τ'' ≤ teichDist τ (g • τ') := by
    intro g
    have := step2 g
    linarith
  have hinf := le_ciInf step3
  have hdef : moduliDist τ τ' = ⨅ x : SL(2, ℤ), teichDist τ (x • τ') := rfl
  rw [← hdef] at hinf
  linarith
