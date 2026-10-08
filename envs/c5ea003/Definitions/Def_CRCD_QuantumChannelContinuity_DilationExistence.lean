-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_DilationExistence
-- name    : CRCD_QuantumChannelContinuity_DilationExistence
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:10:07.548077+00:00
-- url     : https://prove2.me/theorems/954d3d2b-8a7c-445a-9a79-d71ec722ee38
-- title:
--   Isometric CPTP dilations with nonzero finite environments
-- statement:
--   Let $A,B,E$ be finite-dimensional complex Hilbert spaces. If a linear map $V:A\to B\otimes E$ realizes a CPTP map $N$ by
--
--   $$
--   N(X)=\operatorname{Tr}_E(VXV^\dagger),
--   $$
--
--   then $\|Va\|^2=\|a\|^2$ for every $a\in A$. In particular, when $A\ne\{0\}$, every such dilation has $E\ne\{0\}$. Every CPTP map with nonzero input space admits a dilation of this form with a finite-dimensional, nonzero complex environment. The squared-norm identity applies to any supplied CPTP dilation; the environment nontriviality requires the stated nonzero-input hypothesis.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/DilationExistence.lean#L25-L64

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Nontrivial Stinespring environments for quantum channels

Trace preservation excludes a zero-dimensional environment.  This packages the
upstream Stinespring theorem in the form needed by the concrete tensor powers.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B E : Type u} [Qudit A] [Qudit B] [Qudit E]
set_option maxHeartbeats 500000

/-- A dilation of a trace-preserving channel preserves the squared input norm. -/
theorem cptp_dilation_norm_sq (N : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap) (a : A) : ‖V a‖ ^ 2 = ‖a‖ ^ 2 := by
  rw [← trace_dilationChannel_outer_self, hV]
  change (Tr (N.toFun (outer_product a a))).re = _
  rw [← N.trace_map, trace_outer_product]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) a

/-- A channel with nonzero input space cannot have a zero-dimensional
Stinespring environment, including in a supplied nonminimal dilation. -/
theorem nontrivial_environment_of_cptp_dilation [Nontrivial A]
    (N : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap) : Nontrivial E := by
  classical
  by_contra h
  letI : Subsingleton E := not_nontrivial_iff_subsingleton.mp h
  have hz (x : B ⊗[ℂ] E) : x = 0 := by
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b e => rw [Subsingleton.elim e 0]; simp
    | add x y hx hy => simp [hx, hy]
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have hsq := cptp_dilation_norm_sq N V hV a
  rw [hz (V a), norm_zero, zero_pow (by decide : 2 ≠ 0)] at hsq
  apply ha
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg a])

/-- Every actual CPTP channel has a finite nontrivial environment and a
concrete supplied dilation realizing the channel exactly. -/
theorem cptp_has_nontrivial_dilation [Nontrivial A] (N : CPTP A B) :
    ∃ (E : Type u) (_ : Qudit E) (_ : Nontrivial E),
      ∃ V : A →ₗ[ℂ] B ⊗[ℂ] E, dilationChannel V = N.toLinearMap := by
  obtain ⟨E, hE, hV⟩ := cp_to_stinespring (stdOrthonormalBasis ℂ A).toBasis
    N.toLinearMap ⟨N.toCompletelyPositiveMap, rfl⟩
  letI := hE
  obtain ⟨V, hV⟩ := hV
  have hV' : dilationChannel V = N.toLinearMap := by
    ext1 X
    exact (hV X).symm
  exact ⟨E, hE, nontrivial_environment_of_cptp_dilation N V hV', V, hV'⟩

end QuantumChannelContinuity


