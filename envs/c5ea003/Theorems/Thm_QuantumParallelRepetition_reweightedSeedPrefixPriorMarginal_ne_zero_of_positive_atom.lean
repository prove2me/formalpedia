-- Prove2me | Theorems.Thm_QuantumParallelRepetition_reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
-- name    : QuantumParallelRepetition.reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T04:17:35.018734+00:00
-- url     : https://prove2.me/theorems/53060ed2-6921-4418-abb7-528be8af94be
-- title:
--   The reverse prefix prior charges the masked context of every atom of positive posterior
-- statement:
--   Work in the reweighted-seed prefix setting: a finite event law $\lambda$ on an index set $K$, a projection $\Pi : K \times \Omega_{\mathrm{out}} \to \Omega \times V^{h}$ recording a context and an $h$-letter register, a default letter $v_0 \in V$, a marker $k < h$, and a positive postselection mass. Let $q \in K \times \Omega_{\mathrm{out}}$ be a point whose reweighted-seed posterior mass is strictly positive. Then the first marginal of the prefix prior, grouped by the code (prefix mask at $k$, $k$-th letter), is nonzero at the masked flagged context of $q$. This nondegeneracy is what lets one form the conditional distributions of the next letter under the prior at that context.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L55802-L55900

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_21
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (law : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (marker : Fin h)
    (point : K × ExactOutcome X Y A B n)
    (atom_positive :
      0 < reweightedSeedPosterior law G n S D point) :
    jointFirstMarginal
        (groupedMass (exactPrefixNextCode default marker)
          (reweightedSeedPrefixPrior
            law G n S D projection))
        (finitePrefixMask default marker.castSucc
          (((projection point).1,
            repeatedConditionedAnswerFlag
              G n S D point.2),
            (projection point).2)) ≠ 0 := by sorry
