-- Prove2me | solution 1 for Teichmuller.sq_eq_one_of_smul_I_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:16:42.094996+00:00
-- url     : https://prove2.me/submissions/cf8e48e1-03ae-4e72-8051-b728db9b6e38

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
























/-- The only integral solutions of `a² + c² = 1`. -/
theorem int_sq_add_sq_eq_one {a c : ℤ} (h : a ^ 2 + c ^ 2 = 1) :
    (a = 1 ∧ c = 0) ∨ (a = -1 ∧ c = 0) ∨ (a = 0 ∧ c = 1) ∨ (a = 0 ∧ c = -1) := by
  have i1 : -1 ≤ a := by nlinarith [sq_nonneg c, sq_nonneg (a + 1)]
  have i2 : a ≤ 1 := by nlinarith [sq_nonneg c, sq_nonneg (a - 1)]
  have i3 : -1 ≤ c := by nlinarith [sq_nonneg a, sq_nonneg (c + 1)]
  have i4 : c ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg (c - 1)]
  interval_cases a <;> interval_cases c <;> omega






open Teichmuller in
theorem solution(g : SL(2, ℤ)) (h : g • UpperHalfPlane.I = UpperHalfPlane.I) :
    g ^ 2 = 1 ∨ g ^ 2 = -1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.property
    rwa [Matrix.det_fin_two] at this
  have h' : ((g • UpperHalfPlane.I : ℍ) : ℂ) = (UpperHalfPlane.I : ℂ) := by rw [h]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at h'
  simp only [UpperHalfPlane.coe_I, algebraMap_int_eq, eq_intCast] at h'
  push_cast at h'
  have hd : (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * Complex.I +
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) ≠ 0 := by
    intro h0
    rw [Complex.ext_iff] at h0
    simp at h0
    obtain ⟨hd0, hc0⟩ := h0
    have h1 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by exact_mod_cast hd0
    have h2 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by exact_mod_cast hc0
    rw [h1, h2] at hdet; simp at hdet
  rw [div_eq_iff hd, Complex.ext_iff] at h'
  simp at h'
  have had : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := h'.2
  have hbc : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    exact_mod_cast h'.1
  rw [← had, hbc] at hdet
  have hsum : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ^ 2 +
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ^ 2 = 1 := by nlinarith [hdet]
  rcases int_sq_add_sq_eq_one hsum with ⟨ha, hc⟩ | ⟨ha, hc⟩ | ⟨ha, hc⟩ | ⟨ha, hc⟩
  · left; apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, ← had, hbc, ha, hc]
  · left; apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, ← had, hbc, ha, hc]
  · right; apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, ← had, hbc, ha, hc]
  · right; apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, ← had, hbc, ha, hc]
