-- Prove2me | Definitions.Def_Nonadditivity_GeneralBell
-- name    : Nonadditivity_GeneralBell
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:36:48.368392+00:00
-- url     : https://prove2.me/theorems/ecf2ef09-d707-44b9-b29a-4ae6aa988ba4
-- title:
--   Rectangular tensor matrices acting on the Bell vector
-- statement:
--   For finite input and output index sets $I,O$, write $d=|I|$ and $v(i,j)=\sqrt{1/d}\,\mathbf1_{i=j}$. For arbitrary complex matrices $A,B$ with rows indexed by $O$ and columns by $I$, the proved identity is $((A\otimes\overline B)v)(a,b)=\sqrt{1/d}\sum_i A_{ai}\overline{B_{bi}}$. At $d=0$ the source uses zero for the normalization factor. This algebraic identity supplies the entry calculation for paired Bell outputs.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/GeneralBell.lean#L122-L129

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
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




/-! # Bell witnesses for arbitrary Kraus channels

This extends the Bell entropy argument beyond random-unitary complements.
All norms use the Euclidean operator norm, and all states are actual matrices.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.GeneralBell

open Entropy Channels BellOutput
open scoped BigOperators ComplexOrder Matrix Kronecker Matrix.Norms.L2Operator









section BellOverlap

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]



omit [Fintype κ] [Nonempty ι] [Fintype ο] [DecidableEq ο] [Nonempty ο] in
lemma tensor_mul_bell (A B : Matrix ο ι ℂ) (a b : ο) :
    ((A ⊗ₖ B.map star) *ᵥ normalizedBellVector) (a,b) =
      (Real.sqrt (1 / (Fintype.card ι : ℝ)) : ℂ) *
        ∑ i, A a i * star (B b i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.map_apply, normalizedBellVector, bellVector, Finset.mul_sum,
    mul_comm, mul_left_comm]

















end BellOverlap



end Nonadditivity.GeneralBell


