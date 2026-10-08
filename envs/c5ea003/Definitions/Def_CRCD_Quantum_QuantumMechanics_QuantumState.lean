-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState
-- name    : CRCD_Quantum_QuantumMechanics_QuantumState
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:44:25.795882+00:00
-- url     : https://prove2.me/theorems/abab6cb1-faaa-47a9-9fee-d7803f550163
-- title:
--   Finite-dimensional complex Hilbert spaces and operator notation
-- statement:
--   The basic quantum-space structure consists of a complete complex inner-product space $H$ with finite complex dimension, including its normed additive-group structure. It does not require $H$ to be nonzero. The operator and trace interfaces are
--
--   $$L(H)=\operatorname{End}_{\mathbb C}(H),\qquad I_H(x)=x,\qquad\operatorname{Tr}:L(H)\to\mathbb C.$$
--
--   The trace is complex-linear. Inner products use the convention that $\langle x,y\rangle$ is conjugate-linear in $x$ and linear in $y$, and the operator adjoint is the corresponding Hilbert-space adjoint. These definitions and inherited structural instances provide the common finite-dimensional setting for channels, positivity, continuous functional calculus, and entropy expressions.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumMechanics/QuantumState.lean#L17-L39

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.LinearAlgebra.Trace

/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/






namespace QuantumState

universe u v

-- Qudit
class Qudit (a : Type u) extends
  NormedAddCommGroup a,
  InnerProductSpace ℂ a,
  CompleteSpace a,
  FiniteDimensional ℂ a

abbrev L (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : Type u :=
  ℋ →ₗ[ℂ] ℋ

-- Identity operator
abbrev I (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : L ℋ :=
  LinearMap.id

-- Braket notation
notation "⟨" x "∣" y "⟩" => inner ℂ x y

-- Adjoint
notation X "†" => LinearMap.adjoint X

variable {ℋ : Type u} [Qudit ℋ]

-- Trace
noncomputable abbrev Tr : L ℋ →ₗ[ℂ] ℂ := LinearMap.trace ℂ ℋ

-- Normal operators are defined by IsStarNormal


-- Hermitian operators are defined by IsSelfAdjoint


-- Positive semidefinite operators are defined by IsPositive


-- Positive definite operators


-- Projection operators


-- Density operators


-- Unitary operators are defined by unitary


-- Def: Function of normal operators (1.145) of https://cs.uwaterloo.ca/~watrous/TQI/TQI1.pdf
-- For any qudit ℋ, any A ∈ Normal(ℋ), any 𝒳 ⊆ ℂ, and any complex-valued function f: 𝒳 → ℂ,
-- suppose that A's spectral decomposition A=∑_{k=1,…,m} λₖ Πₖ satisfies λₖ ∈ 𝒳 for all k.
-- Then, we define
-- f(A) := ∑_{k=1,…,m} f(λₖ) Πₖ

end QuantumState


