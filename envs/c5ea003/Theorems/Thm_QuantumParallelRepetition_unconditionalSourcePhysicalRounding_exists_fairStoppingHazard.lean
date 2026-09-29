-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalRounding_exists_fairStoppingHazard
-- name    : QuantumParallelRepetition.unconditionalSourcePhysicalRounding_exists_fairStoppingHazard
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:44:03.427537+00:00
-- url     : https://prove2.me/theorems/ada90d53-5a3a-4c66-9e07-c2fde0cb3019
-- title:
--   Existence of grid, horizon and gauge data with fair stopping and hazard bounds for the history ensemble
-- statement:
--   Let $G$ be a finite two-player one-round game, $S$ a strategy for the $n$-fold repetition $G^{\otimes n}$, and
--   $D \subseteq \{1,\dots,n\}$ a set of postselected coordinates with nonempty complement and strictly positive
--   postselection mass $\pi$. Write $d$ for the number of global-history local indices of $(G,n,S,D)$ and
--   $\eta = \bigl(\log(1/\pi) + |D|\log(|\mathcal{A}|\,|\mathcal{B}|)\bigr)/|D^{c}|$ for the martingale rate, and
--   fix $\alpha \in (0,1]$ with $64\sqrt{\eta} + \alpha^{1/3} \le 1$. Then there are a width $w \ge 1$ and
--   positive integers $N, L, B', Q, m$ with
--   $$2(w+1)\frac{d}{N} \le \alpha^{1/3}, \qquad \frac{d}{N} < \frac{1}{w+1}, \qquad
--   \frac{1}{w} + \frac{d\,w}{N} \le \frac{3}{2}\,\alpha^{1/3},$$
--   and two families of unitaries $U^A, U^B$ on $\mathbb{C}^{Nm}$, indexed by a phase $b < B'$ and by an optional
--   natural number, such that, setting $\delta = \alpha^{1/3}$, $t = \sqrt{64\sqrt{\eta} + \delta}$ and
--   $\rho = \alpha^{1/12}$, the following two things hold for the $L$-stage stopping process that uses the width
--   $w$ and the grid $N$ at every stage. First, the width-$w$, grid-$N$ clipped canonical target $\tau_{w,N}$
--   approximates *every* unit vector $\xi \in \mathbb{C}^d \otimes \mathbb{C}^d$, not merely those arising from the
--   game: $\|\xi - \tau_{w,N}(\xi)\|^2 \le \tfrac{3}{2}\delta$. Second, if $h = (i,x,y,r)$ ranges over history
--   tuples distributed according to the locally sampleable law $\mu$ of $(G,n,S,D)$ and the process is run on the
--   pair $(\gamma_{r,x}, \varphi_{r,y})$ of global-history unit vectors that $h$ determines for Alice and for Bob,
--   then
--   $$\sum_h \mu(h)\,\mathrm{Async}(h) \le 64\sqrt{\eta} + \delta, \qquad
--   \sum_h \mu(h)\,\mathrm{Term}(h) \le \delta^2,$$
--   $$\sum_h \mu(h)\,\mathrm{Haz}(h) \;\le\; \frac{34}{t}\bigl(64\sqrt{\eta} + \delta\bigr) + 4\rho^2
--   + \bigl(16(e-1) + 4\bigr)t,$$
--   where $\mathrm{Async}(h)$ is the mass with which the process halts with exactly one party accepting,
--   $\mathrm{Term}(h)$ the mass surviving all $L$ stages, and $\mathrm{Haz}(h)$ the stopped common-prefix hazard of
--   $(U^A, U^B)$ at resolution $Q$ and harmonic size $m$. Thus a single rounding scheme, chosen from $\alpha$ alone,
--   simultaneously controls clipping loss, asynchronous stopping, non-termination and hazard for the conditioned
--   history ensemble.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L68000-L68149

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Theorems.Thm_QuantumParallelRepetition_exactAlicePurificationFamily_posSemidef
import Theorems.Thm_QuantumParallelRepetition_exactBobPurificationFamily_posSemidef
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalSourcePhysicalRounding_exists_fairStoppingHazard
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1) :
    ∃ (w : ℝ) (N L B' Q m : ℕ),
      1 ≤ w ∧ 0 < N ∧ 0 < L ∧ 0 < B' ∧ 0 < Q ∧ 0 < m ∧
      2 * (w + 1) *
          ((Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) : ℝ) / N) ≤
        alpha ^ (1 / 3 : ℝ) ∧
      (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
          (N : ℝ) < 1 / (w + 1) ∧
      (1 / w +
        (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
          w / (N : ℝ) ≤ 3 * alpha ^ (1 / 3 : ℝ) / 2) ∧
      ∃ UA UB : Fin B' → Option ℕ →
          Matrix.unitaryGroup (Fin (N * m)) ℂ,
        let width : Fin 1 → ℝ := fun _ => w
        let schedule : Fin L → Fin 1 := fun _ => 0
        let eta : ℝ := martingaleRate G n S D
        let delta : ℝ := alpha ^ (1 / 3 : ℝ)
        let t : ℝ := Real.sqrt (64 * Real.sqrt eta + delta)
        let rho : ℝ := alpha ^ (1 / 12 : ℝ)
        (∀ ξ : BipartiteUnitVector
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)),
          ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
              w N ξ‖ ^ 2 ≤ 3 * delta / 2) ∧
        ((∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              N width schedule
              (exactGlobalHistoryFinGamma
                G n S D h.2.2.2 h.2.1)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤
            64 * Real.sqrt eta + delta) ∧
        ((∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalTerminalMass
              N width schedule
              (exactGlobalHistoryFinGamma
                G n S D h.2.2.2 h.2.1)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤ delta ^ 2) ∧
        ((∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
              Q m width schedule
              (exactGlobalHistoryFinGamma
                G n S D h.2.2.2 h.2.1)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)
              UA UB) ≤
            (34 / t) * (64 * Real.sqrt eta + delta) +
              4 * rho ^ 2 +
                unconditionalPrefactorBucketCoefficient * t) := by sorry
