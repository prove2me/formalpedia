-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalExactFairStoppedPhaseHarmonicClippedUnit_le
-- name    : QuantumParallelRepetition.unconditionalExactFairStoppedPhaseHarmonicClippedUnit_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:44:34.887957+00:00
-- url     : https://prove2.me/theorems/fae6b774-dbc6-42b3-9241-0b260fe14bd0
-- title:
--   Averaged squared error between the true and clipped verifier states is controlled by the martingale rate
-- statement:
--   Work with a game $G$, a strategy for $G^n$ and a conditioning set $D$ with positive postselected mass and at least one free coordinate. Fix a width $w > 0$, a grid $N > 0$ fine enough that $|\mathcal{I}|/N < 1/(w+1)$ where $\mathcal{I}$ is the global history local index, a phase count $P > 0$ and a harmonic count $m > 0$. For a tuple $u$ let $\psi_u$ be the global source state (which depends on the history, Alice's question and Bob's question) and $\gamma_u$ the corresponding target that ignores Bob's question, and write $\Sigma(v)$ for the coherent phase-sigma state built from the conjugate of $v$ with constant embezzlement work. Then for every family of auxiliary "work" vectors indexed by $(u,k)$ whose rows satisfy $\sum_k \lVert \mathrm{work}(u,k)\rVert^2 \le 1$,
--   $$
--   \sum_{u} P(u) \sum_{k} \Big\lVert\, \Sigma(\psi_u)\otimes \mathrm{work}(u,k) \;-\; \Sigma\big(\gamma_u^{\mathrm{clip}}\big)\otimes \mathrm{work}(u,k) \,\Big\rVert^{2}
--   \;\le\; 16\,\eta \;+\; 8\Big(\tfrac{1}{w} + \tfrac{|\mathcal{I}|\,w}{N}\Big),
--   $$
--   where $P$ is the locally sampleable law, $\gamma_u^{\mathrm{clip}}$ is the canonical accepted unit target obtained by clipping $\gamma_u$ at width $w$ and grid $N$, and $\eta$ is the martingale rate of the conditioning.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L63156-L63227

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_25
import Theorems.Thm_QuantumParallelRepetition_exactAlicePurificationFamily_posSemidef
import Theorems.Thm_QuantumParallelRepetition_exactBobPurificationFamily_posSemidef
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalExactFairStoppedPhaseHarmonicClippedUnit_le
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {w : ℝ} {N P m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (fine :
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1))
    (phases : 0 < P) (harmonic : 0 < m)
    {K : Type*} [Fintype K]
    {T : ExactLocallySampleableTuple X Y A B D × K → Type*}
    [∀ p, Fintype (T p)]
    (work :
      (p : ExactLocallySampleableTuple X Y A B D × K) →
        EuclideanSpace ℂ (T p))
    (work_row :
      ∀ u : ExactLocallySampleableTuple X Y A B D,
        (∑ k : K, ‖work (u, k)‖ ^ 2) ≤ 1) :
    (∑ u : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D u *
        ∑ k : K,
          ‖unconditionalMatchedVerifierTensor
              (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
                P
                (unconditionalConjugatePureVector
                  (exactSourceTuplePsi G n S D u))
                (fun _ _ _ => embezzlementState m))
              (work (u, k)) -
            unconditionalMatchedVerifierTensor
              (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
                P
                (unconditionalConjugatePureVector
                  (dSVDensityRationalCanonicalAcceptedUnitTarget
                    width grid fine
                    (unconditionalExactFairGammaUnit
                      G n S D u)).val)
                (fun _ _ _ => embezzlementState m))
              (work (u, k))‖ ^ 2) ≤
      16 * martingaleRate G n S D +
        8 * (1 / w +
          (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
            w / (N : ℝ)) := by sorry
