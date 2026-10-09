-- Prove2me | Definitions.Def_Nonadditivity_StructuredLinearization
-- name    : Nonadditivity_StructuredLinearization
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:56:28.592588+00:00
-- url     : https://prove2.me/theorems/83464721-68e2-43ac-a69a-79acc49dfd4a
-- title:
--   The product free group for structured channel polynomials
-- statement:
--   For a natural number $n$, the group underlying the structured polynomial construction is the finite product of $n$ copies of the free group on two generators. An element is a function from the $n$ coordinate indices to that free group, with multiplication and inversion performed coordinatewise. This common group type supports the tensor-coordinate and single-factor word constructions.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/StructuredLinearization.lean#L24-L24

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
import Definitions.Def_Nonadditivity_CollinsYoun
import Definitions.Def_Nonadditivity_CollinsYounProduct
import Definitions.Def_Nonadditivity_CollinsYounTensor
import Definitions.Def_Nonadditivity_ComplementaryAdjoint
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FiniteSetFactorization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeCreation
import Definitions.Def_Nonadditivity_FreeEmbedding
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_HaarModel
import Definitions.Def_Nonadditivity_HaarMomentTail
import Definitions.Def_Nonadditivity_InitialNetReduction
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_NetPolynomial
import Definitions.Def_Nonadditivity_NetPolynomialSupport
import Definitions.Def_Nonadditivity_ObservableDimension
import Definitions.Def_Nonadditivity_PolynomialDilation
import Definitions.Def_Nonadditivity_PolynomialReduction
import Definitions.Def_Nonadditivity_ProductPolynomialReduction
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularFactorization
import Definitions.Def_Nonadditivity_RegularFubini
import Definitions.Def_Nonadditivity_RegularRestriction
import Definitions.Def_Nonadditivity_RegularShiftedDilation
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPartitionReduction
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Definitions.Def_Nonadditivity_WordBallReduction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Star.Unitary

namespace Nonadditivity.Quantitative
end Nonadditivity.Quantitative

namespace Nonadditivity.StructuredCostBounds
end Nonadditivity.StructuredCostBounds

namespace Nonadditivity.StructuredReductionCosts
end Nonadditivity.StructuredReductionCosts

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! # Actual structured linearization

The tensor-coordinate partitions and one-factor word balls are applied to the
same polynomial and coefficients, followed by the norm-preserving Hermitian
dilation.  Every intermediate polynomial is explicitly constructed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
namespace Nonadditivity.StructuredLinearization
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open PolynomialReduction

variable {n K : ℕ} [NeZero K]
abbrev G (n : ℕ) := Fin n → FreeGroup (Fin 2)






























section Initial
open FreeModel StructuredCostBounds
variable {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

























end Initial

section ActualNet
open FreeModel FiniteRealization StructuredCostBounds




end ActualNet
end Nonadditivity.StructuredLinearization


