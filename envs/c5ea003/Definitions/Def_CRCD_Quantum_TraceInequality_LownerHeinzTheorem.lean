-- Prove2me | Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
-- name    : CRCD_Quantum_TraceInequality_LownerHeinzTheorem
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:48:51.271872+00:00
-- url     : https://prove2.me/theorems/9ca0f1fb-873d-40e4-a522-0fe77aba40c0
-- title:
--   Fixed-space and uniform Hilbert-space operator convexity
-- statement:
--   For a complete nonzero complex Hilbert space $H$, let $\mathcal B(H)$ be its algebra of bounded complex-linear endomorphisms. It is nontrivial and carries the real continuous functional calculus for selfadjoint elements. For a real function $f$ and a spectral domain $S\subseteq\mathbb R$, fixed-space operator convexity requires
--
--   $$f((1-t)A+tB)\le(1-t)f(A)+t f(B)$$
--
--   for selfadjoint $A,B\in\mathcal B(H)$ with real spectra in $S$ and $0\le t\le1$; operator concavity applies the same predicate to $-f$. The uniform predicates require the corresponding fixed-space property on every complete nonzero complex Hilbert space in the specified universe. Neither fixed-space nor uniform definitions restrict to finite-dimensional spaces, and neither adds continuity of $f$ or convexity of $S$ as a separate condition. These interfaces make the abstract ordered C-star-algebra predicates available for operator Jensen, perspectives, and operator means.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/TraceInequality/LownerHeinzTheorem.lean#L21-L258

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3

/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/







set_option linter.style.longLine false

namespace LownerHeinzTheorem

universe u v

open CFC

abbrev L (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  ℋ →L[ℂ] ℋ

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

noncomputable instance instNontrivialL : Nontrivial (L ℋ) := inferInstance

set_option synthInstance.maxHeartbeats 40000 in
-- Local `synthInstance.maxHeartbeats` for the next `inferInstance`: synthesizing
-- `NonnegSpectrumClass ℝ (L ℋ)` searches a deep superclass/instance chain.
noncomputable local instance : NonnegSpectrumClass ℝ (L ℋ) := inferInstance

set_option synthInstance.maxHeartbeats 80000 in
-- Local `synthInstance.maxHeartbeats` for the next `inferInstance`: synthesizing
-- `ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint` is similarly instance-heavy.
noncomputable instance instCFCRealSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint := inferInstance

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : L ℋ) : L ℋ :=
  LownerHeinzCore.cfcR (𝓐 := L ℋ) f A











/-- Fixed-space operator convexity on `s` for the Hilbert space `ℋ`. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvexOn (𝓐 := L ℋ) s f



/-- Fixed-space operator concavity on `s` for the Hilbert space `ℋ`. -/
def OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcaveOn (𝓐 := L ℋ) s f











omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator convexity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorConvexOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConvexOn (ℋ := K) s f



omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator concavity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConcaveOn (ℋ := K) s f






















theorem power_Icc_zero_one_operatorConcaveOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_zero_one_operatorConcaveOn_Ici (𝓐 := L ℋ) p hp)

theorem power_Icc_one_two_operatorConvexOn_Ici : ∀ p ∈ Set.Icc (1 : ℝ) 2,
    OperatorConvexOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici (𝓐 := L ℋ) p hp)





end LownerHeinzTheorem


