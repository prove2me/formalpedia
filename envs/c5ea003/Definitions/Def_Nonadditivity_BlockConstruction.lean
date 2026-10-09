-- Prove2me | Definitions.Def_Nonadditivity_BlockConstruction
-- name    : Nonadditivity_BlockConstruction
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:37:02.629261+00:00
-- url     : https://prove2.me/theorems/28742647-1f62-4bcd-ae0a-68c9bd3a8cfb
-- title:
--   Standard finite output indices for tensor blocks
-- statement:
--   A tensor chain over a finite index type of cardinality $d$ has cardinality $d^n$ and is nonempty whenever the original type is nonempty. The block channel standardizes the complementary block's output type by an equivalence with a finite index set. Relabeling commutes with channel outputs, complex conjugation, and tensor products, and it preserves the entropy of an original/conjugate joint output, including entangled inputs.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/BlockConstruction.lean#L27-L123

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
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





/-!
# The concrete block channel with standard output coordinates

The tensor block is made from the complementary channels of the actual
uniform random-unitary families. Its output basis alone is relabelled to
`ZMod (K^n)`, with the dimension equality proved here. The Bell witness is
transported from the checked block construction, not supplied as a premise.
-/

noncomputable section

namespace Nonadditivity

open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

namespace Entropy

/-- The empty block has dimension one; each tensor step multiplies dimension. -/
theorem tensorChainIndex_card (ι : Type*) [Fintype ι] (n : ℕ) :
    Fintype.card (TensorChainIndex ι n) = Fintype.card ι ^ n := by
  induction n with
  | zero => simp [TensorChainIndex]
  | succ n ih =>
    change Fintype.card (TensorChainIndex ι n × ι) = _
    simp [ih, pow_succ]

/-- Every finite tensor block of a nonempty index type is nonempty. -/
instance tensorChainIndexNonempty (ι : Type*) [Nonempty ι] :
    (n : ℕ) → Nonempty (TensorChainIndex ι n)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n + 1 => by
    change Nonempty (TensorChainIndex ι n × ι)
    letI := tensorChainIndexNonempty ι n
    infer_instance

@[simp] theorem DensityMatrix.reindex_refl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : ρ.reindex (Equiv.refl ι) = ρ := by
  apply DensityMatrix.ext
  rfl

end Entropy

namespace Channels.KrausChannel

open Entropy

variable {ι ο κ μ ν η : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]

omit [DecidableEq ο] in
/-- Relabeling matrix entries commutes with entrywise complex conjugation. -/
theorem reindex_conjugate_eq [Fintype μ] [DecidableEq μ] [Fintype ν]
    (T : Channels.KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) :
    (T.reindex ei eo).conjugate = T.conjugate.reindex ei eo := by
  apply ext
  funext k
  ext a b
  rfl

omit [DecidableEq ο] in
/-- Relabeling the two tensor factors is relabeling by the product equivalence. -/
theorem reindex_tensor_eq [Fintype μ] [DecidableEq μ] [Fintype ν] [Fintype η]
    {ι' ο' μ' ν' : Type*}
    [Fintype ι'] [DecidableEq ι'] [Fintype ο']
    [Fintype μ'] [DecidableEq μ'] [Fintype ν']
    (T : Channels.KrausChannel ι ο κ) (S : Channels.KrausChannel μ ν η)
    (ei : ι ≃ ι') (eo : ο ≃ ο') (em : μ ≃ μ') (en : ν ≃ ν') :
    (T.reindex ei eo).tensor (S.reindex em en) =
      (T.tensor S).reindex (ei.prodCongr em) (eo.prodCongr en) := by
  apply ext
  funext k
  ext a b
  rfl

/-- Relabel the actual output state together with the actual channel. -/
theorem reindex_output_eq [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (T : Channels.KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) (ρ : DensityMatrix ι) :
    (T.reindex ei eo).output (ρ.reindex ei) = (T.output ρ).reindex eo := by
  apply DensityMatrix.ext
  exact T.reindex_map ei eo ρ.matrix

/-- A common output-basis relabeling preserves the entropy of any original/conjugate
joint output, including entangled inputs. -/
theorem reindex_tensor_conjugate_entropy [Fintype ν] [DecidableEq ν]
    (T : Channels.KrausChannel ι ο κ) (e : ο ≃ ν) (ρ : DensityMatrix (ι × ι)) :
    (((T.reindex (Equiv.refl ι) e).tensor
      (T.reindex (Equiv.refl ι) e).conjugate).output ρ).vonNeumann =
      ((T.tensor T.conjugate).output ρ).vonNeumann := by
  have hi : (Equiv.refl ι).prodCongr (Equiv.refl ι) = Equiv.refl (ι × ι) := by
    ext a <;> rfl
  rw [reindex_conjugate_eq, reindex_tensor_eq, hi]
  have ho := reindex_output_eq (T.tensor T.conjugate) (Equiv.refl (ι × ι)) (e.prodCongr e) ρ
  rw [DensityMatrix.reindex_refl] at ho
  rw [ho, DensityMatrix.reindex_entropy]

end Channels.KrausChannel

namespace BlockConstruction

open Entropy Channels Channels.KrausChannel Conversion
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : ℕ} [NeZero K]

/-- A basis equivalence justified by the actual block's dimension count. -/
def blockOutputEquiv (K n : ℕ) [NeZero K] :
    TensorChainIndex (Fin K) n ≃ ZMod (K ^ n) :=
  Fintype.equivOfCardEq (by simp [tensorChainIndex_card])

/-- The actual tensor block, with the standard `K^n`-dimensional output basis. -/
def blockChannel (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) (n : ℕ) :
    KrausChannel (TensorChainIndex ι n) (ZMod (K ^ n)) (TensorChainIndex ι n) :=
  (BlockBell.blockComplementary U n).reindex (Equiv.refl _) (blockOutputEquiv K n)









end BlockConstruction
end Nonadditivity


