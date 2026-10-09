-- Prove2me | Definitions.Def_Nonadditivity_ActualConsequences
-- name    : Nonadditivity_ActualConsequences
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:47:17.60898+00:00
-- url     : https://prove2.me/theorems/fe209ab4-eeca-4308-a3ff-017d81b21a02
-- title:
--   Actual finite channels and their two-use gap and ratio
-- statement:
--   An actual finite quantum channel packages finite input, output, and Kraus index types together with a Kraus channel; the input and output types are nonempty. Define $\chi(T)$ to be its single-use Holevo information in bits and $\chi_2(T)=\chi(T\otimes T)$. The absolute two-use additivity gap is $\chi_2(T)-2\chi(T)$, and the two-use ratio is $\chi_2(T)/(2\chi(T))$. The ratio has its usual information-theoretic interpretation whenever $\chi(T)>0$.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ActualConsequences.lean#L31-L83

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
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PositiveHolevo
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
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





/-!
# Asymptotic separation for actual finite quantum channels

The channels in this file are actual finite Kraus CPTP maps. They are chosen
from the proved qualitative realization using the specified normalized Haar
matrix model. The two remaining analytic inputs are displayed explicitly:
Collins--Youn's free-operator bound and the canonical Haar strong convergence
statement. No numerical Holevo family or entropy inequality is assumed.

The quantities here are Holevo information in bits. The file makes no
operational-capacity assertion and requires no coding theorem.
-/

noncomputable section

namespace Nonadditivity.ActualConsequences

open Filter Topology
open Nonadditivity.Entropy Nonadditivity.Channels Nonadditivity.Channels.KrausChannel
open scoped BigOperators Matrix ComplexOrder

/-- A packaged finite quantum channel, retaining its genuine Kraus CPTP map
and all finite Hilbert-space and environment indices. -/
structure FiniteQuantumChannel where
  Input : Type
  Output : Type
  Environment : Type
  inputFinite : Fintype Input
  inputDecidable : DecidableEq Input
  inputNonempty : Nonempty Input
  outputFinite : Fintype Output
  outputDecidable : DecidableEq Output
  outputNonempty : Nonempty Output
  environmentFinite : Fintype Environment
  channel : @KrausChannel Input Output Environment inputFinite inputDecidable outputFinite environmentFinite

attribute [instance] FiniteQuantumChannel.inputFinite FiniteQuantumChannel.inputDecidable
  FiniteQuantumChannel.inputNonempty FiniteQuantumChannel.outputFinite
  FiniteQuantumChannel.outputDecidable FiniteQuantumChannel.outputNonempty
  FiniteQuantumChannel.environmentFinite

namespace FiniteQuantumChannel

/-- Package a concrete channel without changing its input, output, or map. -/
def ofKraus {ι ο κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : FiniteQuantumChannel where
  Input := ι
  Output := ο
  Environment := κ
  inputFinite := inferInstance
  inputDecidable := inferInstance
  inputNonempty := inferInstance
  outputFinite := inferInstance
  outputDecidable := inferInstance
  outputNonempty := inferInstance
  environmentFinite := inferInstance
  channel := T

def chi (T : FiniteQuantumChannel) : ℝ := T.channel.holevoBits

def chiTwo (T : FiniteQuantumChannel) : ℝ := (T.channel.tensor T.channel).holevoBits

def gap (T : FiniteQuantumChannel) : ℝ := T.chiTwo - 2 * T.chi

def twoUseRatio (T : FiniteQuantumChannel) : ℝ := T.chiTwo / (2 * T.chi)

@[simp] theorem ofKraus_chi {ι ο κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : (ofKraus T).chi = T.holevoBits := rfl

@[simp] theorem ofKraus_chiTwo {ι ο κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : (ofKraus T).chiTwo = (T.tensor T).holevoBits := rfl





end FiniteQuantumChannel

































end Nonadditivity.ActualConsequences


