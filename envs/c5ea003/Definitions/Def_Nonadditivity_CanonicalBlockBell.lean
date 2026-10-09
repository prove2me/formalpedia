-- Prove2me | Definitions.Def_Nonadditivity_CanonicalBlockBell
-- name    : Nonadditivity_CanonicalBlockBell
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:37:45.839002+00:00
-- url     : https://prove2.me/theorems/3d47d2c1-6a0a-4bce-927b-fa5b95dd13c0
-- title:
--   The canonical Bell state satisfies the block entropy bound
-- statement:
--   The relabeled tensor product of the single-position Bell states is exactly the canonical Bell state on the full tensor-chain index type. For a block of length $n$ built from families of $K$ unitaries, applying the block complementary channel and its conjugate to this state has entropy at most $n(2\log K-(\log K)/K)$. The same estimate holds for the standardized block channel, because output relabeling preserves entropy.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/CanonicalBlockBell.lean#L18-L85

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-! The tensor Bell witness is exactly the canonical Bell density matrix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.CanonicalBlockBell
open Entropy Channels Channels.KrausChannel BlockBell BlockConstruction
open scoped BigOperators Matrix Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem bellState_entry (a b : ι × ι) :
    (BellOutput.bellState (ι := ι)).matrix a b =
      if a.1=a.2 ∧ b.1=b.2 then (Fintype.card ι:ℂ)⁻¹ else 0 := by
  by_cases ha : a.1=a.2 <;> by_cases hb : b.1=b.2 <;>
    simp [BellOutput.bellState,Matrix.vecMulVec,BellOutput.normalizedBellVector,
      bellVector,ha,hb]
  rw [←mul_inv_rev,←Complex.ofReal_mul,Real.mul_self_sqrt (by positivity)]
  simp

theorem blockBellState_eq_canonical (n : ℕ) :
    blockBellState (ι := ι) n = BellOutput.bellState (ι := TensorChainIndex ι n) := by
  induction n with
  | zero =>
    apply DensityMatrix.ext
    ext a b
    rw [bellState_entry]
    rcases a with ⟨a₁,a₂⟩
    rcases b with ⟨b₁,b₂⟩
    cases a₁; cases a₂; cases b₁; cases b₂
    simp [blockBellState,DensityMatrix.tensorChain,DensityMatrix.reindex,
      emptyTensorState,TensorChainIndex]
  | succ n ih =>
    apply DensityMatrix.ext
    ext a b
    rcases a with ⟨⟨a₀,a₁⟩,⟨a₂,a₃⟩⟩
    rcases b with ⟨⟨b₀,b₁⟩,⟨b₂,b₃⟩⟩
    have hx := congrArg (fun ρ : DensityMatrix (TensorChainIndex ι n × TensorChainIndex ι n) =>
      ρ.matrix (a₀,a₂) (b₀,b₂)) ih
    dsimp only at hx
    change (DensityMatrix.tensorChain (fun _ => BellOutput.bellState (ι := ι)) n).matrix
        ((pairChainEquiv ι ι n).symm (a₀,a₂)) ((pairChainEquiv ι ι n).symm (b₀,b₂)) = _ at hx
    change (DensityMatrix.tensorChain (fun _ => BellOutput.bellState (ι := ι)) n).matrix
        ((pairChainEquiv ι ι n).symm (a₀,a₂)) ((pairChainEquiv ι ι n).symm (b₀,b₂)) *
          (BellOutput.bellState (ι := ι)).matrix (a₁,a₃) (b₁,b₃) = _
    rw [hx,bellState_entry,bellState_entry,bellState_entry]
    by_cases ha : a₀=a₂ <;> by_cases hb : b₀=b₂ <;>
      by_cases hc : a₁=a₃ <;> by_cases hd : b₁=b₃ <;>
      simp [ha,hb,hc,hd,TensorChainIndex,Fintype.card_prod,mul_comm]

/-- The explicit complementary-block estimate at the canonical Bell state. -/
theorem block_complementary_canonical_entropy_le {κ : Type*}
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (U : ℕ → κ → unitary (Matrix ι ι ℂ)) (n : ℕ) :
    (((blockComplementary U n).tensor (blockComplementary U n).conjugate).output
      (BellOutput.bellState (ι := TensorChainIndex ι n))).vonNeumann ≤
        (n:ℝ)*(2*Real.log (Fintype.card κ)-Real.log (Fintype.card κ)/(Fintype.card κ:ℝ)) := by
  rw [←blockBellState_eq_canonical]
  let T (j : ℕ) := (KrausChannel.uniformUnitary (U j)).complementary
  have he := pairedTensorChain_output_entropy T (fun j => (T j).conjugate)
    (fun _ => BellOutput.bellState (ι := ι)) n
  rw [←tensorChain_conjugate T n] at he
  calc
    _ = ∑ j ∈ Finset.range n,
        (((T j).tensor (T j).conjugate).output (BellOutput.bellState (ι := ι))).vonNeumann := he
    _ ≤ ∑ j ∈ Finset.range n,
        (2*Real.log (Fintype.card κ)-Real.log (Fintype.card κ)/(Fintype.card κ:ℝ)) :=
      Finset.sum_le_sum (fun j _ => BellOutput.complementary_bell_entropy_le (U j))
    _ = _ := by simp; ring

/-- The actual standardized block channel at the same canonical Bell input. -/
theorem block_channel_canonical_entropy_le {K : ℕ} [NeZero K]
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) (n : ℕ) :
    (((blockChannel U n).tensor (blockChannel U n).conjugate).output
      (BellOutput.bellState (ι := TensorChainIndex ι n))).vonNeumann ≤
        (n:ℝ)*(2*Real.log K-Real.log K/(K:ℝ)) := by
  unfold blockChannel
  rw [reindex_tensor_conjugate_entropy]
  simpa only [Fintype.card_fin] using block_complementary_canonical_entropy_le U n

end Nonadditivity.CanonicalBlockBell


