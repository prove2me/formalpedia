-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceMarkedContextInformation_eq_source
-- name    : QuantumParallelRepetition.exactReverseAliceMarkedContextInformation_eq_source
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T14:26:07.411023+00:00
-- url     : https://prove2.me/theorems/e0d778f8-5ee0-425c-b316-7933a324f3d7
-- title:
--   Alice's reverse marker information at the seed's own coordinate is her per-seed source information
-- statement:
--   Assume $|\bar D| > 0$ and that the postselection mass is positive, and fix a default letter $y_0 \in Y$ and a seed $s$ with distinguished coordinate $i^\ast$. Instantiate Alice's reverse context marker information — the average, over outcomes of the postselected repeated strategy, of the relative entropy between the conditional law of the next Bob question under the reverse-Alice next joint and under the reverse-Alice next prior, given the masked context of the outcome — at the side $\Sigma = \{i^\ast\} \cup L$ determined by $s$, at $s$'s own reverse-Alice context, and at the marker equal to the rank of $i^\ast$ in $\Sigma$. Then this quantity equals Alice's per-seed source Born information
--   $$\sum_{\omega} \Lambda_D(\omega)\; D\Big(P_A\big(\cdot \,\big|\, (i^\ast, x_{i^\ast}),\, \mathrm{hist}(s,\omega)\big)\,\Big\|\, \mu\big(\cdot \mid x_{i^\ast}\big)\Big),$$
--   where $\Lambda_D$ is the law of outcomes conditioned on winning every coordinate of $D$, and $P_A$ is Alice's information posterior. So the reverse-side, per-position information quantity, read at the position corresponding to the seed's own coordinate, is exactly the source-side quantity that the information budget must control.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L56198-L56242

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Theorems.Thm_QuantumParallelRepetition_exactReverseLeftSide_coordinate_mem
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
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
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseAliceMarkedContextInformation_eq_source
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y)
    (seed : ExactRemainingSeed D) :
    exactReverseAliceContextMarkerInformation
        G n S D remaining default
        (exactReverseLeftSide seed)
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
      exactAliceSourceSeedBornInformation
        G n S D seed := by sorry
