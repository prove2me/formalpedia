-- Prove2me | solution 1 for Teichmuller.exists_teichDist_T_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:00:58.846063+00:00
-- url     : https://prove2.me/submissions/cb31b9be-04cc-429e-88d6-da39f433001b

-- Sol generated from Geometry/Teichmuller/ModuliSpace.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_ModuliSpace
import Definitions.Def_Geometry_Teichmuller_TorusSpace
import Definitions.Def_Geometry_Teichmuller_TranslationLength
import Theorems.Thm_Teichmuller_cosh_dist_smul
import Theorems.Thm_Teichmuller_teichDist_eq_half_dist
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

















/-- The displacement of the parabolic class `T : τ ↦ τ + 1`. -/
theorem cosh_dist_T (σ : ℍ) :
    Real.cosh (dist σ (ModularGroup.T • σ)) = 1 + 1 / (2 * σ.im ^ 2) := by
  have h := cosh_dist_smul ModularGroup.T σ
  have hentry : entry ModularGroup.T 0 0 = 1 ∧ entry ModularGroup.T 0 1 = 1 ∧
      entry ModularGroup.T 1 0 = 0 ∧ entry ModularGroup.T 1 1 = 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [entry, ModularGroup.T]
  have htr : tr ModularGroup.T = 2 := by
    simp [tr, hentry.1, hentry.2.2.2]
    norm_num
  rw [htr, hentry.1, hentry.2.1, hentry.2.2.1, hentry.2.2.2] at h
  rw [h]
  ring













open Teichmuller in
theorem solution{ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℍ, teichDist σ (ModularGroup.T • σ) < ε := by
  have hc : 1 < Real.cosh ε := Real.one_lt_cosh.mpr hε.ne'
  set c := Real.cosh ε - 1 with hcdef
  have hcpos : 0 < c := by simp only [hcdef]; linarith
  set y := Real.sqrt (1 / c) + 1 with hydef
  have hy1 : 1 ≤ y := by
    have := Real.sqrt_nonneg (1 / c)
    simp only [hydef]; linarith
  have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
  have hysq : 1 / c < y ^ 2 := by
    have h1 : Real.sqrt (1 / c) ^ 2 = 1 / c := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (1 / c) < y := by simp only [hydef]; linarith
    have h3 : 0 ≤ Real.sqrt (1 / c) := Real.sqrt_nonneg _
    nlinarith
  refine ⟨⟨⟨0, y⟩, hypos⟩, ?_⟩
  set σ : ℍ := ⟨⟨0, y⟩, hypos⟩ with hσ
  have hσim : σ.im = y := rfl
  have hcosh : Real.cosh (dist σ (ModularGroup.T • σ)) < Real.cosh ε := by
    rw [cosh_dist_T, hσim]
    have hkey : 1 / (2 * y ^ 2) < c := by
      rw [div_lt_iff₀ (by positivity)]
      have : 1 / c < y ^ 2 := hysq
      rw [div_lt_iff₀ hcpos] at this
      nlinarith
    simp only [hcdef] at hkey
    linarith
  have hlt : dist σ (ModularGroup.T • σ) < ε := by
    have := Real.cosh_lt_cosh.mp hcosh
    rwa [abs_of_nonneg dist_nonneg, abs_of_pos hε] at this
  rw [teichDist_eq_half_dist]
  linarith
