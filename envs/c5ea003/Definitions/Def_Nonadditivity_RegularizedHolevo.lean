-- Prove2me | Definitions.Def_Nonadditivity_RegularizedHolevo
-- name    : Nonadditivity_RegularizedHolevo
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:48:33.327084+00:00
-- url     : https://prove2.me/theorems/00643a68-1616-4c24-8a88-7fa18bbe1538
-- title:
--   Positive tensor-power channels and normalized Holevo quantities
-- statement:
--   For a type $I$, the positive tensor index is $P_0(I)=I$ and $P_{n+1}(I)=P_n(I)\times I$, so parameter $n\ge0$ represents $n+1$ factors. Finiteness, decidable equality, and nonemptiness are inherited from $I$. For a finite Kraus channel $T$, the bundle constructs genuine tensor-power channels recursively and defines their normalized Holevo information in bits:
--   $$T^{[0]}=T,\qquad T^{[n+1]}=T^{[n]}\otimes T,\qquad h_n(T)=\frac{\chi(T^{[n]})}{n+1}.$$
--   The initial cases satisfy
--   $$h_0(T)=\chi(T),\qquad h_1(T)=\frac{\chi(T\otimes T)}2.$$
--   These definitions and simplification identities supply positive-use channel indices and the normalized finite-power quantities used by the broader released library.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/RegularizedHolevo.lean#L29-L99

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
# Regularized Holevo supremum of actual tensor powers

`positiveTensorPower T n` is the actual Kraus tensor power with `n+1` uses.
Its first two powers are literally `T` and `T.tensor T`; no basis invariance
or assumed tensor-product information law is needed to identify them.
The supremum contains every positive integer number of uses, not a subsequence.

This is a regularized Holevo supremum. No operational coding theorem or
identification with operational classical capacity is asserted here.
-/

noncomputable section

namespace Nonadditivity.RegularizedHolevo

open Nonadditivity.Entropy Nonadditivity.Channels Nonadditivity.ActualConsequences
open scoped Matrix ComplexOrder BigOperators

universe u

/-- Index of a genuine positive tensor power. Index `n` represents `n+1` factors. -/
def PositiveTensorIndex (ι : Type u) : ℕ → Type u
  | 0 => ι
  | n + 1 => PositiveTensorIndex ι n × ι

instance positiveTensorIndexFintype (ι : Type u) [Fintype ι] :
    (n : ℕ) → Fintype (PositiveTensorIndex ι n)
  | 0 => inferInstanceAs (Fintype ι)
  | n + 1 => by
    change Fintype (PositiveTensorIndex ι n × ι)
    letI := positiveTensorIndexFintype ι n
    infer_instance

instance positiveTensorIndexDecidableEq (ι : Type u) [DecidableEq ι] :
    (n : ℕ) → DecidableEq (PositiveTensorIndex ι n)
  | 0 => inferInstanceAs (DecidableEq ι)
  | n + 1 => by
    change DecidableEq (PositiveTensorIndex ι n × ι)
    letI := positiveTensorIndexDecidableEq ι n
    infer_instance

instance positiveTensorIndexNonempty (ι : Type u) [Nonempty ι] :
    (n : ℕ) → Nonempty (PositiveTensorIndex ι n)
  | 0 => inferInstanceAs (Nonempty ι)
  | n + 1 => by
    change Nonempty (PositiveTensorIndex ι n × ι)
    letI := positiveTensorIndexNonempty ι n
    infer_instance



/-- Every positive tensor power is constructed from the actual channel Kraus data. -/
def positiveTensorPower {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) :
    (n : ℕ) → KrausChannel (PositiveTensorIndex ι n) (PositiveTensorIndex ο n)
      (PositiveTensorIndex κ n)
  | 0 => T
  | n + 1 => (positiveTensorPower T n).tensor T

@[simp] theorem positiveTensorPower_zero {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : positiveTensorPower T 0 = T := rfl

@[simp] theorem positiveTensorPower_one {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : positiveTensorPower T 1 = T.tensor T := rfl

/-- The normalized Holevo information of the actual `n+1`-use tensor power. -/
def normalizedPowerHolevo {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) (n : ℕ) : ℝ :=
  (positiveTensorPower T n).holevoBits / ((n + 1 : ℕ) : ℝ)

@[simp] theorem normalizedPowerHolevo_zero {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : normalizedPowerHolevo T 0 = T.holevoBits := by
  simp [normalizedPowerHolevo, positiveTensorPower, PositiveTensorIndex,
    positiveTensorIndexFintype, positiveTensorIndexDecidableEq]
  rfl

@[simp] theorem normalizedPowerHolevo_one {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : normalizedPowerHolevo T 1 = (T.tensor T).holevoBits / 2 := rfl



end Nonadditivity.RegularizedHolevo

namespace Nonadditivity.ActualConsequences.FiniteQuantumChannel

open Nonadditivity.RegularizedHolevo























end Nonadditivity.ActualConsequences.FiniteQuantumChannel

namespace Nonadditivity.ActualConsequences

open Filter Topology











end Nonadditivity.ActualConsequences


