-- Prove2me | Definitions.Def_Nonadditivity_BlockBell
-- name    : Nonadditivity_BlockBell
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:35:25.871389+00:00
-- url     : https://prove2.me/theorems/6f69b596-057f-4680-91b8-9f8a24e09862
-- title:
--   Bell states for blocks of complementary channels
-- statement:
--   A block Bell state is obtained by tensoring one Bell state per position and relabeling the paired indices. The block complementary channel is the tensor chain of the single-position complementary channels. Reindexing and conjugation commute with the relevant tensor constructions, and paired block outputs on product inputs are tensor chains of paired local outputs. Their entropy is therefore the sum of the local output entropies.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/BlockBell.lean#L25-L156

import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_TensorPowers
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
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
# Actual Bell witnesses for finite complementary-channel tensor blocks

The tensor output factorization is proved by regrouping the actual Kraus
coordinates with a recursive basis equivalence. Thus the entangled block
witness and its entropy bound are derived from the local Bell estimate.
-/

noncomputable section

namespace Nonadditivity.BlockBell

open Nonadditivity.Entropy Nonadditivity.Channels
open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

/-- Complex conjugation commutes with the concrete Kraus tensor product. -/
theorem tensor_conjugate {ι μ ο ν κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    [Fintype ο] [DecidableEq ο] [Fintype ν] [DecidableEq ν]
    [Fintype κ] [Fintype η]
    (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η) :
    (T.tensor S).conjugate = T.conjugate.tensor S.conjugate := by
  apply KrausChannel.ext
  funext k
  ext i j
  simp [KrausChannel.tensor, KrausChannel.conjugate, Matrix.kroneckerMap_apply,
    Matrix.map_apply]

/-- Conjugating the full actual tensor block conjugates each local channel. -/
theorem tensorChain_conjugate {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : ℕ → KrausChannel ι ο κ) (n : ℕ) :
    (KrausChannel.tensorChain T n).conjugate =
      KrausChannel.tensorChain (fun j => (T j).conjugate) n := by
  induction n with
  | zero =>
    apply KrausChannel.ext
    funext k
    ext i j
    simp [KrausChannel.tensorChain, KrausChannel.emptyTensorChannel,
      KrausChannel.conjugate, Matrix.map_apply]
  | succ n ih =>
    change ((KrausChannel.tensorChain T n).tensor (T n)).conjugate = _
    rw [tensor_conjugate, ih]
    rfl

/-- Regrouping all input, output and Kraus labels gives the exact block
Kraus coefficient; no output-factorization property is assumed. -/
lemma tensorChain_paired_kraus {ι μ ο ν κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    [Fintype ο] [DecidableEq ο] [Fintype ν] [DecidableEq ν]
    [Fintype κ] [Fintype η]
    (T : ℕ → KrausChannel ι ο κ) (S : ℕ → KrausChannel μ ν η) (n : ℕ)
    (k : TensorChainIndex κ n × TensorChainIndex η n)
    (a : TensorChainIndex ο n × TensorChainIndex ν n)
    (b : TensorChainIndex ι n × TensorChainIndex μ n) :
    (KrausChannel.tensorChain (fun j => (T j).tensor (S j)) n).kraus
      ((pairChainEquiv κ η n).symm k)
      ((pairChainEquiv ο ν n).symm a)
      ((pairChainEquiv ι μ n).symm b) =
    ((KrausChannel.tensorChain T n).tensor (KrausChannel.tensorChain S n)).kraus k a b := by
  induction n with
  | zero =>
    simp [KrausChannel.tensorChain, KrausChannel.emptyTensorChannel,
      KrausChannel.tensor, Matrix.kroneckerMap_apply]
  | succ n ih =>
    rcases k with ⟨⟨k₀,k₁⟩, ⟨l₀,l₁⟩⟩
    rcases a with ⟨⟨a₀,a₁⟩, ⟨c₀,c₁⟩⟩
    rcases b with ⟨⟨b₀,b₁⟩, ⟨d₀,d₁⟩⟩
    simp only [pairChainEquiv_succ_symm_apply, KrausChannel.tensorChain,
      KrausChannel.tensor, Matrix.kroneckerMap_apply]
    have hp := ih (k₀,l₀) (a₀,c₀) (b₀,d₀)
    simp only [KrausChannel.tensor, Matrix.kroneckerMap_apply] at hp
    rw [hp]
    ring

/-- The exact equality of the interleaved and paired channel blocks after
reindexing their three finite coordinate systems. -/
theorem tensorChain_pair_reindex {ι μ ο ν κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    [Fintype ο] [DecidableEq ο] [Fintype ν] [DecidableEq ν]
    [Fintype κ] [Fintype η]
    (T : ℕ → KrausChannel ι ο κ) (S : ℕ → KrausChannel μ ν η) (n : ℕ) :
    (((KrausChannel.tensorChain (fun j => (T j).tensor (S j)) n).reindex
      (pairChainEquiv ι μ n) (pairChainEquiv ο ν n)).reindexKraus (pairChainEquiv κ η n)) =
      (KrausChannel.tensorChain T n).tensor (KrausChannel.tensorChain S n) := by
  apply KrausChannel.ext
  funext k
  ext a b
  exact tensorChain_paired_kraus T S n k a b

lemma reindex_output {ι μ ο ν κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    [Fintype ο] [DecidableEq ο] [Fintype ν] [DecidableEq ν] [Fintype κ]
    (T : KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) (ρ : DensityMatrix ι) :
    (T.reindex ei eo).output (ρ.reindex ei) = (T.output ρ).reindex eo := by
  apply DensityMatrix.ext
  exact T.reindex_map ei eo ρ.matrix

lemma reindexKraus_output {ι ο κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο]
    [Fintype κ] [Fintype η] (T : KrausChannel ι ο κ) (e : κ ≃ η)
    (ρ : DensityMatrix ι) : (T.reindexKraus e).output ρ = T.output ρ := by
  apply DensityMatrix.ext
  exact T.reindexKraus_map e ρ.matrix

/-- A tensor of local paired inputs, regrouped into the two input blocks,
produces precisely the regrouped tensor of the local paired outputs. -/
theorem pairedTensorChain_output {ι μ ο ν κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    [Fintype ο] [DecidableEq ο] [Fintype ν] [DecidableEq ν]
    [Fintype κ] [Fintype η]
    (T : ℕ → KrausChannel ι ο κ) (S : ℕ → KrausChannel μ ν η)
    (ρ : ℕ → DensityMatrix (ι × μ)) (n : ℕ) :
    ((KrausChannel.tensorChain T n).tensor (KrausChannel.tensorChain S n)).output
        ((DensityMatrix.tensorChain ρ n).reindex (pairChainEquiv ι μ n)) =
      (DensityMatrix.tensorChain (fun j => ((T j).tensor (S j)).output (ρ j)) n).reindex
        (pairChainEquiv ο ν n) := by
  rw [← tensorChain_pair_reindex T S n, reindexKraus_output, reindex_output,
    KrausChannel.tensorChain_output]

/-- The genuine entangled paired-block output has the sum of its local
paired-output entropies, as a consequence of the proved matrix identity. -/
theorem pairedTensorChain_output_entropy {ι μ ο ν κ η : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    [Fintype ο] [DecidableEq ο] [Fintype ν] [DecidableEq ν]
    [Fintype κ] [Fintype η]
    (T : ℕ → KrausChannel ι ο κ) (S : ℕ → KrausChannel μ ν η)
    (ρ : ℕ → DensityMatrix (ι × μ)) (n : ℕ) :
    (((KrausChannel.tensorChain T n).tensor (KrausChannel.tensorChain S n)).output
        ((DensityMatrix.tensorChain ρ n).reindex (pairChainEquiv ι μ n))).vonNeumann =
      ∑ j ∈ Finset.range n, (((T j).tensor (S j)).output (ρ j)).vonNeumann := by
  rw [pairedTensorChain_output, DensityMatrix.reindex_entropy,
    DensityMatrix.tensorChain_entropy]

/-- The actual tensor block of the local random-unitary complementary channels. -/
def blockComplementary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (U : ℕ → κ → unitary (Matrix ι ι ℂ)) (n : ℕ) :
    KrausChannel (TensorChainIndex ι n) (TensorChainIndex κ n) (TensorChainIndex ι n) :=
  KrausChannel.tensorChain (fun j => (KrausChannel.uniformUnitary (U j)).complementary) n

/-- The actual Bell tensor input witness, in the paired block coordinates. -/
def blockBellState {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ℕ) :
    DensityMatrix (TensorChainIndex ι n × TensorChainIndex ι n) :=
  (DensityMatrix.tensorChain (fun _ => BellOutput.bellState (ι := ι)) n).reindex
    (pairChainEquiv ι ι n)



end Nonadditivity.BlockBell


