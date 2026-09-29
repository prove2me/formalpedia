-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalSameGridWeightedStoppingLedger
-- name    : QuantumParallelRepetition.unconditionalSourcePhysicalSameGridWeightedStoppingLedger
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T18:56:42.491525+00:00
-- url     : https://prove2.me/theorems/4cff7b06-a8fd-43ac-b55f-cfafe35629e5
-- title:
--   A single-width stopping ledger for a weighted ensemble of bipartite vector pairs
-- statement:
--   Fix a dimension $d \ge 1$ and a grid resolution $N \ge 1$, a width $w \ge 1$ and a precision
--   $\delta \in (0,1]$ subject to the grid budget $2(w+1)\,d/N \le \delta$, together with two further
--   parameters $t \in (0,1]$ and $\rho > 0$. Let $(\mu_i)_{i \in I}$ be a probability vector on a finite index
--   set $I$, let $\xi_i, \zeta_i$ be unit vectors of $\mathbb{C}^d \otimes \mathbb{C}^d$, and suppose their
--   weighted energy obeys $\sum_i \mu_i \|\xi_i - \zeta_i\|^2 \le 32\eta$ for a real number $\eta$. Then one
--   can choose, once and for all and uniformly in $i$, a horizon $L \ge 1$, a phase count $B \ge 1$, a bucket
--   resolution $Q \ge 1$ and a harmonic size $m \ge 1$, together with two families of unitaries $A_b(\cdot)$ and
--   $C_b(\cdot)$ on $\mathbb{C}^{Nm}$ indexed by a phase $b < B$ and by an optional natural number, such that the
--   $L$-stage stopping process that runs the width-$w$, grid-$N$ threshold test at *every* one of its stages
--   satisfies the five bounds below. Here $\mathrm{Async}_i$ is the mass with which the process on the pair
--   $(\xi_i,\zeta_i)$ halts with exactly one of the two parties accepting, $\mathrm{Term}_i$ is the mass that
--   survives all $L$ stages without halting, and $\mathrm{Haz}_i$ is the stopped common-prefix hazard, namely the
--   sum over stages $j < L$ of the mass of the length-$j$ common-prefix failure vector times the squared distance
--   between the ideal coherent target state and the state produced by the local reset built from $(A,C)$ at
--   resolution $Q$ and harmonic size $m$:
--   $$\text{(a) } \mathrm{Async}_i \le 8\sqrt{2}\,\|\xi_i - \zeta_i\| + \delta, \qquad
--   \text{(b) } \mathrm{Term}_i \le \delta^2 \qquad \text{for every } i;$$
--   $$\text{(c) } \sum_i \mu_i\,\mathrm{Async}_i \le 64\sqrt{\eta} + \delta, \qquad
--   \text{(d) } \sum_i \mu_i\,\mathrm{Term}_i \le \delta^2,$$
--   $$\text{(e) } \sum_i \mu_i\,\mathrm{Haz}_i \;\le\; \frac{34}{t}\bigl(64\sqrt{\eta} + \delta\bigr)
--   + 4\rho^2 + \bigl(16(e-1) + 4\bigr)t.$$
--   The point of the lemma is that a single discretisation -- one width, one grid, one horizon, one pair of
--   unitary families -- serves the whole ensemble at once, and that the weighted bounds (c)-(e) depend on the
--   ensemble only through its energy parameter $\eta$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L66428-L66567

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalSourcePhysicalSameGridWeightedStoppingLedger
    {d N : ℕ} (dimension : 0 < d) (grid : 0 < N)
    (w δ : ℝ) (large : 1 ≤ w)
    (precision : 0 < δ) (bounded : δ ≤ 1)
    (grid_budget : 2 * (w + 1) * ((d : ℝ) / N) ≤ δ)
    (t : ℝ) (t_positive : 0 < t) (t_bounded : t ≤ 1)
    (rho : ℝ) (rho_positive : 0 < rho)
    {ι : Type} [Fintype ι]
    (weight : ι → ℝ)
    (weight_nonnegative : ∀ i, 0 ≤ weight i)
    (weight_normalized : (∑ i, weight i) = 1)
    (ξ ζ : ι → BipartiteUnitVector d)
    (eta : ℝ)
    (source_energy :
      (∑ i, weight i * ‖(ξ i).val - (ζ i).val‖ ^ 2) ≤ 32 * eta) :
    ∃ L B Q m : ℕ,
      0 < L ∧ 0 < B ∧ 0 < Q ∧ 0 < m ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * m)) ℂ,
        let width : Fin 1 → ℝ := fun _ => w
        let schedule : Fin L → Fin 1 := fun _ => 0
        (∀ i,
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              N width schedule (ξ i) (ζ i) ≤
            8 * Real.sqrt 2 * ‖(ξ i).val - (ζ i).val‖ + δ) ∧
        (∀ i,
          dSVDensityRationalHeterogeneousPhysicalTerminalMass
              N width schedule (ξ i) (ζ i) ≤ δ ^ 2) ∧
        ((∑ i, weight i *
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
            N width schedule (ξ i) (ζ i)) ≤
              64 * Real.sqrt eta + δ) ∧
        ((∑ i, weight i *
          dSVDensityRationalHeterogeneousPhysicalTerminalMass
            N width schedule (ξ i) (ζ i)) ≤ δ ^ 2) ∧
        ((∑ i, weight i *
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
            Q m width schedule (ξ i) (ζ i) A C) ≤
          (34 / t) * (64 * Real.sqrt eta + δ) +
            4 * rho ^ 2 +
              (16 * (Real.exp 1 - 1) + 4) * t) := by sorry
