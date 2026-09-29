-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceRoundingContext_clippingBound
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_clippingBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T22:03:47.225213+00:00
-- url     : https://prove2.me/theorems/d9b6ff09-27b4-4783-b15c-c20911d3ba78
-- title:
--   The rounding context's clipping energy is bounded by the martingale rate and the rounding parameter
-- statement:
--   Let $G$ be a game on finite alphabets $X, Y, A, B$, let $S$ be a strategy for the $n$-fold
--   repetition $G^{n}$, let $D \subseteq \{0,\dots,n-1\}$ be the postselected coordinate set, and let
--   $\alpha, \gamma \in \mathbb{R}$ be the rounding and slack parameters. Suppose $c$ is an
--   `UnconditionalActualFairSourceRoundingContext` for these data — the bundle carrying the sampler,
--   the stopping schedule, the operator and actual families, and the hypotheses they must satisfy.
--
--   Then the clipping energy of the context obeys
--
--   $$
--   \mathrm{clipping}(c) \;\le\; 16 \cdot \mathrm{martingaleRate}(G, n, S, D)
--     \;+\; 8 \cdot \frac{3\,\alpha^{1/3}}{2}.
--   $$
--
--   The clipping energy measures how much weight the protocol discards when it truncates the
--   rounded operators to the admissible range. The bound says that loss is controlled by two things
--   only: the martingale rate of the postselected strategy, and the rounding parameter $\alpha$
--   through $\alpha^{1/3}$. It is one of the four ledger bounds the rounding context supplies to the
--   stopped-verifier estimate.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70417-L70432

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
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
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
open UnconditionalActualFairSourceRoundingContext
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_clippingBound
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    clipping c ≤
      16 * martingaleRate G n S D +
        8 * (3 * alpha ^ (1 / 3 : ℝ) / 2) := by sorry
