-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.tendsto_normalizedZetaSystemFactor_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:34:14.701942+00:00
-- url     : https://prove2.me/submissions/d44aef57-4b08-4b74-83c6-a13e6739470c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Uniform zeta control near the pole at one

Mathlib completes the singular function

`z ↦ z * riemannZeta (1 + z)`

across `z = 0` by means of the entire function `riemannZeta₁`.  This file
packages that completion in the coordinates used by the
Goldston--Yıldırım argument.  In particular, the completed residue factor
is uniformly close to one on a small complex ball, and the corresponding
two-variable normalized zeta ratio is uniformly close to one on a small
polydisc.

The latter is the stable way to state the zeta comparison: all apparent
singularities have already been removed.  Separate lemmas recover the raw
zeta expressions away from zero.
-/

/-
The completion definitions and their differentiability proofs below are
backported from Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean at
 db584cd6d46c92f209a44c0f1c829460d327499d.
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Terence Tao
-/
section GreenTaoZetaCompatibility

open Set Filter Complex
open scoped Topology





@[simp]
lemma riemannZeta₀_one : riemannZeta₀ 1 = (Real.eulerMascheroniConstant : ℂ) := by simp [riemannZeta₀]

@[simp]
lemma riemannZeta₁_one : riemannZeta₁ 1 = 1 := by simp [riemannZeta₁]





@[fun_prop]
lemma differentiable_riemannZeta₀ : Differentiable ℂ riemannZeta₀ := by
  rw [← differentiableOn_univ, ← differentiableOn_compl_singleton_and_continuousAt_iff
    (univ_mem : _ ∈ 𝓝 (1 : ℂ)), continuousAt_iff_punctured_nhds, ← compl_eq_univ_diff]
  constructor
  · refine .congr (f := fun s ↦ riemannZeta s - (s - 1)⁻¹) ?_ (by simp +contextual [riemannZeta₀])
    exact differentiableOn_riemannZeta.fun_sub (by fun_prop (disch := grind))
  · convert tendsto_nhdsWithin_congr ?_ tendsto_riemannZeta_sub_one_div <;>
    simp +contextual [riemannZeta₀]

@[fun_prop]
lemma differentiable_riemannZeta₁ : Differentiable ℂ riemannZeta₁ := by
  unfold riemannZeta₁; fun_prop

end GreenTaoZetaCompatibility

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology



@[simp]
theorem zetaResidueFactor_zero :
    zetaResidueFactor 0 = 1 := by
  simp [zetaResidueFactor]



theorem differentiable_zetaResidueFactor :
    Differentiable ℂ zetaResidueFactor := by
  unfold zetaResidueFactor
  fun_prop

theorem continuous_zetaResidueFactor :
    Continuous zetaResidueFactor :=
  differentiable_zetaResidueFactor.continuous











@[simp]
theorem normalizedZetaPairFactor_zero_zero :
    normalizedZetaPairFactor 0 0 = 1 := by
  simp [normalizedZetaPairFactor]

theorem continuousAt_normalizedZetaPairFactor_zero :
    ContinuousAt
      (fun z : ℂ × ℂ =>
        normalizedZetaPairFactor z.1 z.2)
      (0, 0) := by
  have hnum :
      ContinuousAt
        (fun z : ℂ × ℂ =>
          zetaResidueFactor (z.1 + z.2))
        (0, 0) := by
    exact continuous_zetaResidueFactor.continuousAt.comp
      (by fun_prop)
  have hden :
      ContinuousAt
        (fun z : ℂ × ℂ =>
          zetaResidueFactor z.1 *
            zetaResidueFactor z.2)
        (0, 0) := by
    exact
      (continuous_zetaResidueFactor.continuousAt.comp
          (by fun_prop)).mul
        (continuous_zetaResidueFactor.continuousAt.comp
          (by fun_prop))
  exact hnum.div hden (by simp)

theorem tendsto_normalizedZetaPairFactor_zero :
    Tendsto
      (fun z : ℂ × ℂ =>
        normalizedZetaPairFactor z.1 z.2)
      (𝓝 (0, 0)) (𝓝 1) := by
  simpa only [normalizedZetaPairFactor_zero_zero] using
    continuousAt_normalizedZetaPairFactor_zero.tendsto





/-! ## Finite systems of paired zeta factors -/













end Wikipedia.SzemeredisTheorem

end
/-!
# Uniform zeta control near the pole at one

Mathlib completes the singular function

`z ↦ z * riemannZeta (1 + z)`

across `z = 0` by means of the entire function `riemannZeta₁`.  This file
packages that completion in the coordinates used by the
Goldston--Yıldırım argument.  In particular, the completed residue factor
is uniformly close to one on a small complex ball, and the corresponding
two-variable normalized zeta ratio is uniformly close to one on a small
polydisc.

The latter is the stable way to state the zeta comparison: all apparent
singularities have already been removed.  Separate lemmas recover the raw
zeta expressions away from zero.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## Finite systems of paired zeta factors -/

open Wikipedia.SzemeredisTheorem in
/-- A finite product of the completed pair factors still tends to one
uniformly as all parameters tend to zero. -/
theorem solution
    {κ : Type*} [Fintype κ] :
    Tendsto
      (fun z : (κ → ℂ) × (κ → ℂ) =>
        normalizedZetaSystemFactor z.1 z.2)
      (𝓝 (0, 0)) (𝓝 1) := by
  classical
  have hfactor :
      ∀ i ∈ (Finset.univ : Finset κ),
        Tendsto
          (fun z : (κ → ℂ) × (κ → ℂ) =>
            normalizedZetaPairFactor
              (z.1 i) (z.2 i))
          (𝓝 (0, 0)) (𝓝 1) := by
    intro i _
    have hcoord :
        ContinuousAt
          (fun z : (κ → ℂ) × (κ → ℂ) =>
            (z.1 i, z.2 i))
          (0, 0) := by
      fun_prop
    change
      Tendsto
        ((fun z : ℂ × ℂ =>
            normalizedZetaPairFactor z.1 z.2) ∘
          (fun z : (κ → ℂ) × (κ → ℂ) =>
            (z.1 i, z.2 i)))
        (𝓝 (0, 0)) (𝓝 1)
    exact
      tendsto_normalizedZetaPairFactor_zero.comp
        hcoord.tendsto
  simpa [normalizedZetaSystemFactor] using
    (tendsto_finsetProd
      (s := (Finset.univ : Finset κ)) hfactor)
