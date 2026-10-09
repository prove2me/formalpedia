-- Prove2me | Definitions.Def_Nonadditivity_HolevoRateLimit
-- name    : Nonadditivity_HolevoRateLimit
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:51:10.81513+00:00
-- url     : https://prove2.me/theorems/845bef8a-fe5e-4599-9382-bfe2b9baa0a9
-- title:
--   The Holevo information sequence of tensor powers
-- statement:
--   For a finite Kraus channel $T$, define a real sequence whose zeroth term is zero and whose $(n+1)$st term is the bit-valued Holevo information of the actual $(n+1)$-fold tensor power of $T$. The zero and successor identities expose this definition to subsequent tensor-power calculations. Each nonzero term uses the same ensemble-supremum definition of Holevo information as the original channel.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/HolevoRateLimit.lean#L89-L97

import Definitions.Def_Nonadditivity_ActualConsequences
import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Asymptotics
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_BlockScalars
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ComplementaryAdjoint
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_HaarModel
import Definitions.Def_Nonadditivity_HolevoBits
import Definitions.Def_Nonadditivity_HolevoTensorSuperadditivity
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PositiveHolevo
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_RegularizedHolevo
import Definitions.Def_Nonadditivity_Scalar
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Subadditive
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Star.Unitary

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # The regularized Holevo supremum is the actual tensor-power rate limit

We prove tensor-power superadditivity using actual product ensembles and an
explicit associativity equivalence of the input, output and Kraus bases, then
apply Fekete's lemma. No operational coding theorem is asserted.
-/

noncomputable section

namespace Nonadditivity.RegularizedHolevo

open Entropy Channels Channels.KrausChannel ActualConsequences
open Filter Topology
open scoped Kronecker Matrix

universe u



variable {ι ο κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]







/-- Unnormalized actual tensor-power Holevo information, with the zero-use
value defined to be zero. Positive entries retain all actual channel data. -/
def powerHolevo (T : KrausChannel ι ο κ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (positiveTensorPower T n).holevoBits

@[simp] theorem powerHolevo_zero (T : KrausChannel ι ο κ) : powerHolevo T 0 = 0 := rfl
@[simp] theorem powerHolevo_succ (T : KrausChannel ι ο κ) (n : ℕ) :
    powerHolevo T (n + 1) = (positiveTensorPower T n).holevoBits := rfl



end Nonadditivity.RegularizedHolevo

namespace Nonadditivity.ActualConsequences.FiniteQuantumChannel

open Nonadditivity.RegularizedHolevo
open Filter Topology



end Nonadditivity.ActualConsequences.FiniteQuantumChannel


