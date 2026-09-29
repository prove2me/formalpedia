-- Prove2me | Theorems.Thm_QuantumParallelRepetition_directDSVActualStoppingSelectedHistory_sourceProduct
-- name    : QuantumParallelRepetition.directDSVActualStoppingSelectedHistory_sourceProduct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T18:54:35.875048+00:00
-- url     : https://prove2.me/theorems/b5281759-3d8b-41c9-aa73-488ea23e80ad
-- title:
--   Amplitude of a commonly stopped history factors into selected copy, failing prefix, and untouched tail
-- statement:
--   Fix $L$ rounds, a family of widths $(w_s)_{s < S}$ and a schedule assigning a width index to each round, bipartite unit vectors $\xi, \zeta$ of local dimension $d$, and a round $j$. Suppose Alice's and Bob's local histories are each presented in split form: a selected index at position $j$, a prefix of $j$ indices before it, and a tail of $L - j$ indices after it. Then the amplitude of the heterogeneous actual physical state at that pair of histories is the product of three amplitudes:
--   $$
--   \Psi\big(h_A, h_B\big) \;=\;
--   \mathrm{Out}_{w_{\sigma(j)}}\big(\text{accept},\text{accept}\big)\big(\text{selected pair}\big)
--   \ \cdot\
--   \mathrm{Fail}_{<j}\big(\text{prefix pair}\big)
--   \ \cdot\
--   \mathrm{Shared}_{L-j}\big(\text{tail pair}\big),
--   $$
--   namely the complete projective outcome at the scheduled width with both accept flags set to true evaluated at the selected pair, the stopped common-prefix failure amplitude at the prefix pair, and the independent shared-state amplitude at the tail pair. Stopping at round $j$ thus decouples the state into "what happened at the stopping copy", "what failed before it", and "what was never touched".
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L60552-L60681

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.directDSVActualStoppingSelectedHistory_sourceProduct
    {S N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (selectedA selectedB : DSVUniformDensityThresholdLocalIndex N d)
    (beforeA beforeB : Fin j.val →
      DSVUniformDensityThresholdLocalIndex N d)
    (afterA afterB : Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ
        (⟨j.succ,
          directDSVSelectedCopyLocalHistoryEquiv j
            (selectedA, (beforeA, afterA))⟩,
         ⟨j.succ,
          directDSVSelectedCopyLocalHistoryEquiv j
            (selectedB, (beforeB, afterB))⟩) =
      dSVDensityRationalCompleteProjectiveOutcome
          (width (schedule j)) N ξ ζ true true
          (selectedA, selectedB) *
        dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j
          (fun i => (beforeA i, beforeB i)) *
        dSVUniformDensityIndependentSharedState
          (L - j.val) N d (afterA, afterB) := by sorry
