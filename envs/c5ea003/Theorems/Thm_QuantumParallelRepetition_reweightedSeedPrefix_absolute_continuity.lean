-- Prove2me | Theorems.Thm_QuantumParallelRepetition_reweightedSeedPrefix_absolute_continuity
-- name    : QuantumParallelRepetition.reweightedSeedPrefix_absolute_continuity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T03:32:00.779308+00:00
-- url     : https://prove2.me/theorems/c9d943a7-e5b7-4e87-8e52-7fb13af546bf
-- title:
--   The prefix joint law is absolutely continuous with respect to the prefix reference law
-- statement:
--   Keep the setting of the previous item: $P=\lambda\otimes\mathbb{P}_S$ is the prior on $K\times\Omega$, $Q$ is its conditioning on the event that $S$ wins every coordinate of $D$ (assumed to have positive probability), $f:K\times\Omega\to\Omega_0\times V^{h}$ is a projection, and $Z=A^{D}\times B^{D}$ is the answer flag. On the index set $(\Omega_0\times Z)\times V^{h}$ consider the joint law $J$, obtained by pushing $Q$ forward along $q\mapsto(f(q),\text{answers}_D(q))$ and rearranging coordinates, and the reference $R=(f_{*}P)\otimes\mathrm{Unif}(Z)$ rearranged the same way. The theorem states that $J$ is absolutely continuous with respect to $R$ pointwise: for every point $t$, $R(t)=0$ implies $J(t)=0$. This is the side condition required by the chain rule for the prefix relative entropies built from $J$ and $R$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L32316-L32372

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_21
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.reweightedSeedPrefix_absolute_continuity
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (t : (Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) :
    reweightedSeedPrefixPrior
        seedLaw G n S D projection t = 0 →
      reweightedSeedPrefixJoint
        seedLaw G n S D projection t = 0 := by sorry
