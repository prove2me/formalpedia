-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceRoundingData_exists_stoppedVerifier
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceRoundingData_exists_stoppedVerifier
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T21:02:58.71559+00:00
-- url     : https://prove2.me/theorems/60abb4ab-e33b-41ef-8563-cd083ba2e040
-- title:
--   Rounding a repeated strategy to a one-copy strategy with an explicit winning lower bound
-- statement:
--   Let $G$ be a game with finite alphabets, $S$ a strategy for $G^{\otimes n}$, and $D\subseteq\{0,\dots,n-1\}$ a coordinate set such that (a) at least one coordinate lies outside $D$; (b) the postselected mass $\Pr[\,S\text{ wins every coordinate of }D\,]$ is positive; and (c) the average conditional failure probability of $S$ over the coordinates outside $D$ is strictly below $(1-\omega^*(G))/2$. Let $\alpha\in(0,1]$ and $\gamma>0$, write $\lambda$ for the martingale rate of $(G,n,S,D)$, $\beta:=64\sqrt{\lambda}+\alpha^{1/3}$, $\kappa:=16(e-1)+4$, and $\pi$ for the Pinsker rate $\sqrt{\tfrac12 I}$ attached to the exact source (with $I$ the classical information rate), and assume $\beta\le 1$. Then there exist real numbers $\mathrm{dev},\mathrm{clip}$ and a strategy $T$ for the **single** game $G$ such that
--   $$\mathrm{dev}\le \frac{34}{\sqrt\beta}\beta + 4\big(\alpha^{1/12}\big)^2 + \kappa\sqrt\beta,\qquad \mathrm{clip}\le 16\lambda + 8\cdot\tfrac{3\alpha^{1/3}}{2},$$
--   $$\omega(T)\;\ge\;1-\frac{1-\omega^*(G)}{2}-5\big(\pi+\gamma\big)-\Big(\big(\beta+(\alpha^{1/3})^{2}\big)+4\sqrt{\mathrm{dev}}+2\sqrt{\mathrm{clip}}\Big).$$
--   This is the crux of the whole argument: a repeated strategy that is only rarely refuted on the coordinates outside $D$ can be converted into a one-copy strategy winning $G$ with probability essentially $1-\tfrac{1-\omega^*(G)}{2}$, which contradicts the definition of $\omega^*(G)$ once the error terms are small.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70791-L70843

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_28
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairSourceRoundingData_exists_stoppedVerifier
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (failure :
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D <
        (1 - entangledValue G) / 2) :
    ∃ (deviation clipping : ℝ) (rounded : Strategy G),
      (deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ))) ∧
      (clipping ≤
        16 * martingaleRate G n S D +
          8 * (3 * alpha ^ (1 / 3 : ℝ) / 2)) ∧
      (1 - (1 - entangledValue G) / 2 -
        5 * (exactSourcePinskerRate G n S D + gamma) -
          ((64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ) +
              (alpha ^ (1 / 3 : ℝ)) ^ 2) +
            4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
        rounded.winProbability) := by sorry
