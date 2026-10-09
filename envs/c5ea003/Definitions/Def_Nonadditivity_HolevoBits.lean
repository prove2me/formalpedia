-- Prove2me | Definitions.Def_Nonadditivity_HolevoBits
-- name    : Nonadditivity_HolevoBits
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:41:51.045062+00:00
-- url     : https://prove2.me/theorems/53d4dc5a-985b-43d4-8a07-210c6418a717
-- title:
--   Conversion of finite-channel Holevo information to bits
-- statement:
--   The bit-valued Holevo information of a finite Kraus channel is its ensemble-defined Holevo information divided by $\log2$. A natural-logarithm bound of the form $\chi\le n\log(1+9/K)+\eta\log2$ therefore becomes $\chi/\log2\le n\log_2(1+9/K)+\eta$. This conversion changes the numerical convention while preserving the underlying channel and ensemble supremum.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/HolevoBits.lean#L24-L55

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
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_Scalar
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

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# The actual channel bounds in the manuscript's base-two convention

The underlying Holevo information is defined on finite ensembles of genuine
quantum output states.  Division by the positive constant `log 2` converts
the proved natural-logarithm results without changing any channel or model.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

def holevoBits (T : KrausChannel ι ο κ) : ℝ := T.holevo / Real.log 2

@[simp] theorem holevoBits_def (T : KrausChannel ι ο κ) :
    T.holevoBits = T.holevo / Real.log 2 := rfl





end Nonadditivity.Channels.KrausChannel

namespace Nonadditivity.HolevoBits

open Entropy Channels Channels.KrausChannel AdjointPurity BlockConstruction Conversion Scalar
open scoped Matrix.Norms.L2Operator

theorem natural_upper_to_bits {K χ η : ℝ} (n : ℕ)
    (h : χ ≤ (n : ℝ) * Real.log (1 + 9 / K) + η * Real.log 2) :
    χ / Real.log 2 ≤ (n : ℝ) * aK K + η := by
  apply (div_le_iff₀ log_two_pos).mpr
  have he : ((n : ℝ) * aK K + η) * Real.log 2 =
      (n : ℝ) * Real.log (1 + 9 / K) + η * Real.log 2 := by
    dsimp [aK, log2]
    field_simp
  rw [he]
  exact h



variable {K : ℕ} [NeZero K]



end Nonadditivity.HolevoBits


