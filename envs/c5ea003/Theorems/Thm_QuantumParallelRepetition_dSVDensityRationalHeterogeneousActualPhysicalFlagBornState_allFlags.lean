-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousActualPhysicalFlagBornState_allFlags
-- name    : QuantumParallelRepetition.dSVDensityRationalHeterogeneousActualPhysicalFlagBornState_allFlags
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T08:02:25.248576+00:00
-- url     : https://prove2.me/theorems/0458ae9f-eb33-4552-8ff7-9d164e51e6da
-- title:
--   The flagged heterogeneous protocol state factorizes across copies once both stopping flags are fixed
-- statement:
--   Consider the heterogeneous stopped embezzlement protocol with $L$ stages, stage widths given by $\mathrm{width}:\{1,\dots,S\}\to\mathbb R$ composed with a schedule $\{1,\dots,L\}\to\{1,\dots,S\}$, run on the threshold resource determined by two bipartite unit vectors $\xi,\zeta\in\mathbb C^d\otimes\mathbb C^d$. Each party's whole-history register is a pair consisting of a stopping flag in $\{0,\dots,L\}$ and a history assigning one local threshold index to each of the $L+1$ copies. The theorem computes the amplitude of the global physical state on an arbitrary product basis vector with Alice data $(f_A,a)$ and Bob data $(f_B,b)$: it equals the product over copies $i=0,\dots,L$ of the single-copy stopped-outcome amplitude at $(a_i,b_i)$, where copy $i$ uses width $\mathrm{width}(\mathrm{schedule}(i))$ for $i<L$ and width $0$ for the terminal copy, and where each party's local outcome at copy $i$ (reject before its flag, accept at its flag, unmeasured after) is read off from that party's flag. In other words, conditioned on the pair of flags the state is a tensor product across the $L+1$ copies.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L42583-L42645

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
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
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable

theorem
    QuantumParallelRepetition.dSVDensityRationalHeterogeneousActualPhysicalFlagBornState_allFlags
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (flagAlice flagBob : Fin (L + 1))
    (alice bob : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ
        (⟨flagAlice, alice⟩, ⟨flagBob, bob⟩) =
      ∏ i : Fin (L + 1),
        dSVDensityRationalCompleteStoppedOptionalOutcome
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ ζ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagAlice i)
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagBob i) (alice i, bob i) := by sorry
