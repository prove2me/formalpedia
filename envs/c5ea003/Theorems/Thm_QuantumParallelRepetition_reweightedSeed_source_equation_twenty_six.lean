-- Prove2me | Theorems.Thm_QuantumParallelRepetition_reweightedSeed_source_equation_twenty_six
-- name    : QuantumParallelRepetition.reweightedSeed_source_equation_twenty_six
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T03:47:42.443294+00:00
-- url     : https://prove2.me/theorems/793959a2-b2b8-4c4d-b4d8-1b8c0008c391
-- title:
--   Total prefix entropy increment is bounded by the postselection cost plus the answer cost
-- statement:
--   With $G$, $S$, $D$, the auxiliary law $\lambda$ on $K$, the prior $P=\lambda\otimes\mathbb{P}_S$ and the postselected law $Q$ as above (assuming $\varepsilon=\mathbb{P}_S[W_D]>0$), fix a projection $f:K\times\Omega\to\Omega_0\times V^{h}$ whose second component is a string of $h$ symbols from $V$, and let $Z=A^{D}\times B^{D}$ record the answers of both players on the coordinates of $D$. Compare the joint law, the pushforward of $Q$ under $q\mapsto(f(q),\text{answers}_D(q))$, with the reference $(f_{*}P)\otimes\mathrm{Unif}(Z)$, both regarded as laws on $(\Omega_0\times Z)\times V^{h}$. For $0\le k\le h$ let $\Lambda_k$ be the relative entropy of these two laws after all symbols of index $\ge k$ are overwritten by a fixed default value, so $\Lambda_k$ only sees the length-$k$ prefix, and let $\Delta_k=\Lambda_{k+1}-\Lambda_k$ be the $k$-th increment. The theorem, equation (26) of the source argument, asserts $$\sum_{k=0}^{h-1}\Delta_k\;\le\;\log\frac{1}{\varepsilon}+|D|\log\big(|A|\,|B|\big).$$
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L32165-L32223

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
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
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

theorem QuantumParallelRepetition.reweightedSeed_source_equation_twenty_six
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) :
    (∑ k : Fin h,
      reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k) ≤
      postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by sorry
