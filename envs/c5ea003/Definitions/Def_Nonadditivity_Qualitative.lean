-- Prove2me | Definitions.Def_Nonadditivity_Qualitative
-- name    : Nonadditivity_Qualitative
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:40:17.692989+00:00
-- url     : https://prove2.me/theorems/44b78353-e10c-431c-b4e7-849d411eaee9
-- title:
--   Exact input dimension of the block construction
-- statement:
--   Let $K>0$ and $n\ge0$ be integers, let $I$ be a finite local matrix index set of cardinality $N$, and let $I_n(I)$ denote the recursively nested $n$-fold tensor index. The input index of the switched, Weyl-extended block construction has cardinality
--   $$\left|\bigl(\mathbb Z/(K^n\mathbb Z)\bigr)^2\times\bigl(\{0,1\}\times I_n(I)\bigr)\right|=2N^nK^{2n}.$$
--   The two residue coordinates encode the Weyl labels, and the Boolean coordinate encodes the switch. This bundle supplies the exact combinatorial dimension identity used after the finite local realization has been chosen.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Qualitative.lean#L30-L37

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_BlockScalars
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
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Nonadditivity.FiniteChannelRealization
end Nonadditivity.FiniteChannelRealization

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # Qualitative realization by actual finite quantum channels

All Bell, entropy, finite-net, switch, and Weyl steps are proved. The
remaining premises are an upper bound on the limiting observable norm and
convergence in probability of the concrete finite block adjoints. There is
no assumed finite-matrix norm certificate or assumed Holevo inequality.

The entropies and Holevo quantities in this module use natural logarithms.
-/

noncomputable section

namespace Nonadditivity.Qualitative

open Entropy Channels Channels.KrausChannel AdjointPurity
open BlockConstruction Conversion BlockScalars
open scoped Matrix.Norms.L2Operator

variable {K : ℕ} [NeZero K]

/-- The exact input dimension of the constructed channel, before any
quantitative choice of the local matrix dimension is made. -/
theorem constructed_input_dimension (ι : Type*) [Fintype ι] (n : ℕ) :
    Fintype.card ((ZMod (K ^ n) × ZMod (K ^ n)) × (Bool × TensorChainIndex ι n)) =
      2 * Fintype.card ι ^ n * K ^ (2 * n) := by
  simp only [Fintype.card_prod, ZMod.card, Fintype.card_bool, tensorChainIndex_card]
  rw [show 2 * n = n * 2 by omega, pow_mul]
  ring









end Nonadditivity.Qualitative


