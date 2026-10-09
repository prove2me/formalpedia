-- Prove2me | Definitions.Def_Nonadditivity_ChannelTensorControl
-- name    : Nonadditivity_ChannelTensorControl
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:22.679593+00:00
-- url     : https://prove2.me/theorems/e01f6187-8c0f-40f3-9a4a-04f742749fc4
-- title:
--   Joint inputs for controlled tensor channels
-- statement:
--   For finite input spaces $I,J$, finite classical label sets, and chosen labels $z,w$, this bundle embeds any density matrix on $\mathbb C^{I\times J}$ into the joint labelled input space. Rectangular selector matrices recover that state at the chosen label pair. The proved identities show that applying the two controlled channels produces the same output as the selected tensor channel; output unitary conjugations commute with this construction.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ChannelTensorControl.lean#L30-L117

import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# Two-use control embeddings and output unitaries

Classical labels are attached to arbitrary joint density matrices, including
entangled inputs. The controlled tensor channel then applies the selected two
branches to that same joint state.
-/

noncomputable section

namespace Nonadditivity.Channels

open Entropy
open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

variable {ι ο κ ζ μ ν η ξ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο]
variable [Fintype κ] [Fintype ζ] [DecidableEq ζ]
variable [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
variable [Fintype η] [Fintype ξ] [DecidableEq ξ]

/-- Select one classical label in each half of a joint input. -/
def jointSelector (z : ζ) (w : ξ) : Matrix (ι × μ) ((ζ × ι) × (ξ × μ)) ℂ :=
  selector z ⊗ₖ selector w

theorem jointSelector_mul_adjoint (z z' : ζ) (w w' : ξ) :
    jointSelector (ι := ι) (μ := μ) z w * (jointSelector (ι := ι) (μ := μ) z' w').conjTranspose =
      if z = z' ∧ w = w' then 1 else 0 := by
  rw [jointSelector, jointSelector, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, selector_mul_adjoint, selector_mul_adjoint]
  by_cases hz : z = z' <;> by_cases hw : w = w' <;>
    simp [hz, hw]

/-- Embed any joint state while fixing both classical input labels. -/
def jointLabelledState (z : ζ) (w : ξ) (ρ : DensityMatrix (ι × μ)) :
    DensityMatrix ((ζ × ι) × (ξ × μ)) where
  matrix := (jointSelector z w).conjTranspose * ρ.matrix * jointSelector z w
  positive := ρ.positive.conjTranspose_mul_mul_same _
  normalized := by
    rw [Matrix.trace_mul_cycle, jointSelector_mul_adjoint]
    simp [ρ.normalized]

/-- Every other label block vanishes; the selected block is the original joint state. -/
theorem select_jointLabelledState (z z' : ζ) (w w' : ξ) (ρ : DensityMatrix (ι × μ)) :
    jointSelector z w * (jointLabelledState z' w' ρ).matrix *
      (jointSelector z w).conjTranspose =
      if z = z' ∧ w = w' then ρ.matrix else 0 := by
  change jointSelector z w *
    ((jointSelector z' w').conjTranspose * ρ.matrix * jointSelector z' w') *
    (jointSelector z w).conjTranspose = _
  have hmat : jointSelector z w *
      ((jointSelector z' w').conjTranspose * ρ.matrix * jointSelector z' w') *
      (jointSelector z w).conjTranspose =
      (jointSelector z w * (jointSelector z' w').conjTranspose) * ρ.matrix *
      (jointSelector z' w' * (jointSelector z w).conjTranspose) := by
    simp only [Matrix.mul_assoc]
  rw [hmat, jointSelector_mul_adjoint, jointSelector_mul_adjoint]
  by_cases hz : z = z' <;> by_cases hw : w = w' <;>
    simp [hz, hw, eq_comm]

namespace KrausChannel

omit [DecidableEq ο] [DecidableEq ν] in
/-- Expand a tensor of controlled channels as its concrete pair of measured blocks. -/
theorem controlled_tensor_map (T : ζ → KrausChannel ι ο κ)
    (S : ξ → KrausChannel μ ν η)
    (X : Matrix ((ζ × ι) × (ξ × μ)) ((ζ × ι) × (ξ × μ)) ℂ) :
    ((controlled T).tensor (controlled S)).map X =
      ∑ z, ∑ w, ((T z).tensor (S w)).map
        (jointSelector z w * X * (jointSelector z w).conjTranspose) := by
  simp only [map, tensor, controlled, jointSelector, Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_mul, Fintype.sum_prod_type, Matrix.mul_assoc]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_comm]

/-- Two fixed classical labels select the corresponding two channel branches on
an arbitrary entangled density matrix. -/
@[simp] theorem controlled_tensor_output_labelled (T : ζ → KrausChannel ι ο κ)
    (S : ξ → KrausChannel μ ν η) (z : ζ) (w : ξ) (ρ : DensityMatrix (ι × μ)) :
    ((controlled T).tensor (controlled S)).output (jointLabelledState z w ρ) =
      ((T z).tensor (S w)).output ρ := by
  apply DensityMatrix.ext
  simp only [output_matrix, controlled_tensor_map, select_jointLabelledState]
  simp [ite_and, apply_ite, map_zero]

/-- Tensoring two output conjugations is conjugation by the tensor unitary,
also for entangled inputs. -/
theorem tensor_outputUnitary_map (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η)
    (U : unitary (Matrix ο ο ℂ)) (V : unitary (Matrix ν ν ℂ))
    (X : Matrix (ι × μ) (ι × μ) ℂ) :
    ((T.outputUnitary U).tensor (S.outputUnitary V)).map X =
      ((T.tensor S).outputUnitary (tensorUnitary U V)).map X := by
  have hk (k : κ × η) :
      ((T.outputUnitary U).tensor (S.outputUnitary V)).kraus k =
        ((T.tensor S).outputUnitary (tensorUnitary U V)).kraus k := by
    exact Matrix.mul_kronecker_mul _ _ _ _
  simp only [map, hk]

/-- The actual joint output states satisfy the tensor-unitary conjugation identity. -/
theorem tensor_outputUnitary_output (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η)
    (U : unitary (Matrix ο ο ℂ)) (V : unitary (Matrix ν ν ℂ))
    (ρ : DensityMatrix (ι × μ)) :
    ((T.outputUnitary U).tensor (S.outputUnitary V)).output ρ =
      ((T.tensor S).output ρ).unitaryConjugate (tensorUnitary U V) := by
  apply DensityMatrix.ext
  change ((T.outputUnitary U).tensor (S.outputUnitary V)).map ρ.matrix = _
  rw [tensor_outputUnitary_map, outputUnitary_map]
  rfl

end KrausChannel
end Nonadditivity.Channels


