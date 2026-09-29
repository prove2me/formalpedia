-- Prove2me | solution 1 for Teichmuller.exists_order_three_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:00:57.74514+00:00
-- url     : https://prove2.me/submissions/13368d8f-2f7d-4c94-90ef-39946a1591f0

-- Sol generated from Geometry/Teichmuller/ModuliSpace.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_ModuliSpace
import Definitions.Def_Geometry_Teichmuller_TranslationLength
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























/-- The elliptic class `ST : τ ↦ -1/(τ + 1)` fixes the hexagonal torus. -/
theorem smul_rho : (ModularGroup.S * ModularGroup.T) • rho = rho := by
  rw [SemigroupAction.mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : ((rho : ℂ) + 1) * (rho : ℂ) = -1 := by
    apply Complex.ext <;> simp [rho] <;> nlinarith [h3]
  simp only [UpperHalfPlane.coe_vadd]
  push_cast
  exact inv_eq_of_mul_eq_one_left (by linear_combination -key)







open Teichmuller in
theorem solution:
    ∃ g : SL(2, ℤ), g • rho = rho ∧ g ^ 3 = -1 ∧ g ≠ 1 ∧ g ≠ -1 ∧ g ^ 2 ≠ 1 ∧ g ^ 2 ≠ -1 := by
  refine ⟨ModularGroup.S * ModularGroup.T, smul_rho, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp [ModularGroup.S, ModularGroup.T, pow_succ, Matrix.one_fin_two]
  · intro h
    have h00 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    simp [ModularGroup.S, ModularGroup.T] at h00
  · intro h
    have h00 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    simp [ModularGroup.S, ModularGroup.T] at h00
  · intro h
    have h01 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
    simp [ModularGroup.S, ModularGroup.T, pow_succ] at h01
  · intro h
    have h01 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
    simp [ModularGroup.S, ModularGroup.T, pow_succ] at h01
