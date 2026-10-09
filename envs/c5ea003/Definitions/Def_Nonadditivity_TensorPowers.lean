-- Prove2me | Definitions.Def_Nonadditivity_TensorPowers
-- name    : Nonadditivity_TensorPowers
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:15.56766+00:00
-- url     : https://prove2.me/theorems/e53be7ee-709c-4396-b41c-690a1fd17888
-- title:
--   Finite tensor chains of states and channels
-- statement:
--   Finite tensor chains are defined recursively, starting from the one-dimensional empty product. The interface equips their index types with finite decidable structure and supplies the equivalence between a tensor chain of pairs and a pair of tensor chains. Product inputs pass through the corresponding tensor chain of channels componentwise, and the entropy of a tensor chain of states or product outputs is the sum of the component entropies.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/TensorPowers.lean#L24-L202

import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-!
# Finite tensor blocks of genuine density matrices and channels

The Hilbert-space indices are nested products. Block states and channels
are defined recursively using their actual Kronecker products, and the
entropy identities are proved by induction from the concrete binary law.
-/

namespace Nonadditivity.Entropy

open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

noncomputable section

universe u

/-- Index type of a finite block, with the empty block the one-dimensional space. -/
def TensorChainIndex (ι : Type u) : ℕ → Type u
  | 0 => PUnit.{u + 1}
  | n + 1 => TensorChainIndex ι n × ι

instance tensorChainIndexFintype (ι : Type u) [Fintype ι] :
    (n : ℕ) → Fintype (TensorChainIndex ι n)
  | 0 => inferInstanceAs (Fintype PUnit.{u + 1})
  | n + 1 => by
    change Fintype (TensorChainIndex ι n × ι)
    letI := tensorChainIndexFintype ι n
    infer_instance

instance tensorChainIndexDecidableEq (ι : Type u) [DecidableEq ι] :
    (n : ℕ) → DecidableEq (TensorChainIndex ι n)
  | 0 => inferInstanceAs (DecidableEq PUnit.{u + 1})
  | n + 1 => by
    change DecidableEq (TensorChainIndex ι n × ι)
    letI := tensorChainIndexDecidableEq ι n
    infer_instance

universe v

/-- Regroup a finite interleaved tensor index into its two tensor blocks. -/
def pairChainEquiv (ι : Type u) (μ : Type v) :
    (n : ℕ) → TensorChainIndex (ι × μ) n ≃ TensorChainIndex ι n × TensorChainIndex μ n
  | 0 =>
    { toFun := fun _ => (PUnit.unit, PUnit.unit)
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by rcases x with ⟨a,b⟩; cases a; cases b; rfl }
  | n + 1 =>
    { toFun := fun x =>
        let a := (pairChainEquiv ι μ n) x.1
        ((a.1, x.2.1), (a.2, x.2.2))
      invFun := fun x =>
        ((pairChainEquiv ι μ n).symm (x.1.1, x.2.1), (x.1.2, x.2.2))
      left_inv := fun x => by
        rcases x with ⟨a, ⟨i,j⟩⟩
        simp
      right_inv := fun x => by
        rcases x with ⟨⟨a,i⟩, ⟨b,j⟩⟩
        simp }

@[simp] theorem pairChainEquiv_succ_apply (ι : Type u) (μ : Type v) (n : ℕ)
    (a : TensorChainIndex (ι × μ) n) (i : ι) (j : μ) :
    pairChainEquiv ι μ (n + 1) (a, (i,j)) =
      (((pairChainEquiv ι μ n a).1, i), ((pairChainEquiv ι μ n a).2, j)) := rfl

@[simp] theorem pairChainEquiv_succ_symm_apply (ι : Type u) (μ : Type v) (n : ℕ)
    (a : TensorChainIndex ι n) (b : TensorChainIndex μ n) (i : ι) (j : μ) :
    (pairChainEquiv ι μ (n + 1)).symm ((a,i),(b,j)) =
      ((pairChainEquiv ι μ n).symm (a,b), (i,j)) := rfl

/-- The unique density matrix of the one-dimensional empty tensor block. -/
def emptyTensorState : DensityMatrix PUnit.{u + 1} where
  matrix := 1
  positive := Matrix.PosSemidef.one
  normalized := by simp [Matrix.trace_one]

theorem emptyTensorState_entropy : emptyTensorState.{u}.vonNeumann = 0 := by
  apply le_antisymm
  · simpa using emptyTensorState.{u}.vonNeumann_le_log_dim
  · exact emptyTensorState.{u}.vonNeumann_nonneg

/-- An actual finite tensor block of an arbitrary state family. -/
def DensityMatrix.tensorChain {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ρ : ℕ → DensityMatrix ι) : (n : ℕ) → DensityMatrix (TensorChainIndex ι n)
  | 0 => emptyTensorState
  | n + 1 => (tensorChain ρ n).tensor (ρ n)

theorem DensityMatrix.tensorChain_entropy {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ρ : ℕ → DensityMatrix ι) (n : ℕ) :
    (tensorChain ρ n).vonNeumann = ∑ j ∈ Finset.range n, (ρ j).vonNeumann := by
  induction n with
  | zero =>
    change emptyTensorState.{u}.vonNeumann = 0
    exact emptyTensorState_entropy
  | succ n ih =>
    calc
      (tensorChain ρ (n + 1)).vonNeumann = (tensorChain ρ n).vonNeumann +
          (ρ n).vonNeumann := (tensorChain ρ n).tensor_entropy (ρ n)
      _ = ∑ j ∈ Finset.range (n + 1), (ρ j).vonNeumann := by
        rw [ih, Finset.sum_range_succ]



end

end Nonadditivity.Entropy

namespace Nonadditivity.Channels.KrausChannel

open Nonadditivity.Entropy
open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

noncomputable section

/-- Concrete tensor channels produce the concrete tensor of their product-input outputs. -/
theorem tensor_output {ι μ ο ν κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    [Fintype ο] [DecidableEq ο] [Fintype ν] [DecidableEq ν]
    [Fintype κ] [Fintype η]
    (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η)
    (ρ : DensityMatrix ι) (σ : DensityMatrix μ) :
    (T.tensor S).output (ρ.tensor σ) = (T.output ρ).tensor (S.output σ) := by
  apply Nonadditivity.Channels.densityMatrix_ext
  exact T.tensor_map S ρ.matrix σ.matrix



universe u v w

/-- The empty channel sends the unique one-dimensional input state to its unique output state. -/
def emptyTensorChannel :
    KrausChannel PUnit.{u + 1} PUnit.{v + 1} PUnit.{w + 1} where
  kraus := fun _ _ _ => 1
  complete := by
    ext i j
    cases i
    cases j
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem emptyTensorChannel_output :
    emptyTensorChannel.{u,v,w}.output emptyTensorState.{u} = emptyTensorState.{v} := by
  apply Nonadditivity.Channels.densityMatrix_ext
  ext i j
  cases i
  cases j
  simp [output, map, emptyTensorChannel, emptyTensorState, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/-- The actual tensor block of a local Kraus-channel family. -/
def tensorChain {ι : Type u} {ο : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : ℕ → KrausChannel ι ο κ) :
    (n : ℕ) → KrausChannel (TensorChainIndex ι n) (TensorChainIndex ο n)
      (TensorChainIndex κ n)
  | 0 => emptyTensorChannel
  | n + 1 => (tensorChain T n).tensor (T n)

/-- Actual tensor blocks map actual product states to actual products of local outputs. -/
theorem tensorChain_output {ι : Type u} {ο : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : ℕ → KrausChannel ι ο κ) (ρ : ℕ → DensityMatrix ι) (n : ℕ) :
    (tensorChain T n).output (DensityMatrix.tensorChain ρ n) =
      DensityMatrix.tensorChain (fun j => (T j).output (ρ j)) n := by
  induction n with
  | zero => exact emptyTensorChannel_output
  | succ n ih =>
    change ((tensorChain T n).tensor (T n)).output
      ((DensityMatrix.tensorChain ρ n).tensor (ρ n)) =
        (DensityMatrix.tensorChain (fun j => (T j).output (ρ j)) n).tensor
          ((T n).output (ρ n))
    exact (tensor_output (tensorChain T n) (T n) (DensityMatrix.tensorChain ρ n) (ρ n)).trans
      (congrArg (fun q : DensityMatrix (TensorChainIndex ο n) =>
        q.tensor ((T n).output (ρ n))) ih)

/-- Exact entropy sum for the outputs of a genuine finite channel tensor block. -/
theorem tensorChain_output_entropy {ι : Type u} {ο : Type v} {κ : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : ℕ → KrausChannel ι ο κ) (ρ : ℕ → DensityMatrix ι) (n : ℕ) :
    ((tensorChain T n).output (DensityMatrix.tensorChain ρ n)).vonNeumann =
      ∑ j ∈ Finset.range n, ((T j).output (ρ j)).vonNeumann := by
  rw [tensorChain_output, DensityMatrix.tensorChain_entropy]



end

end Nonadditivity.Channels.KrausChannel


