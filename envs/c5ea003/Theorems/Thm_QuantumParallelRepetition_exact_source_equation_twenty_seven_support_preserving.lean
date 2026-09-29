-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exact_source_equation_twenty_seven_support_preserving
-- name    : QuantumParallelRepetition.exact_source_equation_twenty_seven_support_preserving
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T14:58:03.465507+00:00
-- url     : https://prove2.me/theorems/7372ca8d-1f89-48f6-aab4-7d17f73300cb
-- title:
--   Support-preserving rounding of the local samplers to a common denominator (equation 27)
-- statement:
--   Let $P$ be the locally sampleable law on tuples (free coordinate, Alice question, Bob question, history flag) induced by a strategy for $G^n$ conditioned on winning all coordinates of $D$, and let $J_A$ and $J_B$ be Alice's and Bob's locally sampleable approximations relative to a base history flag. Assume the postselected mass is positive, at least one coordinate is free, $\gamma > 0$, and $d_{\mathrm{TV}}(P, J_A) \le \kappa$ and $d_{\mathrm{TV}}(P, J_B) \le \kappa$. Then a support-preserving classical sampler exists: there are a positive integer denominator $m$ and integer numerators $\nu(\mathrm{index}, \cdot)$ summing to $m$ for each local index, such that every rounded local conditional $\nu(\mathrm{index},\cdot)/m$ is within $\gamma$ in total variation of the true local conditional, every history of positive conditional probability receives a strictly positive numerator, and moreover
--   $$
--   d_{\mathrm{TV}}\big(P, J_A^{\mathrm{rnd}}\big) \le \kappa + \gamma, \qquad
--   d_{\mathrm{TV}}\big(P, J_B^{\mathrm{rnd}}\big) \le \kappa + \gamma, \qquad
--   \Pr[\text{shared-permutation outputs disagree}] \le 4(\kappa + \gamma).
--   $$
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L57441-L57543

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exact_source_equation_twenty_seven_support_preserving
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {kappa gamma : ℝ} (gamma_positive : 0 < gamma)
    (alice : finiteTotalVariation
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJA G n S D base) ≤ kappa)
    (bob : finiteTotalVariation
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJB G n S D base) ≤ kappa) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base kappa gamma := by sorry
