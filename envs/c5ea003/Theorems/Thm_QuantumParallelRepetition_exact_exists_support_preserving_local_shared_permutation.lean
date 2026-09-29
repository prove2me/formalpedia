-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exact_exists_support_preserving_local_shared_permutation
-- name    : QuantumParallelRepetition.exact_exists_support_preserving_local_shared_permutation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T03:40:52.145728+00:00
-- url     : https://prove2.me/theorems/80b92da9-8217-48a5-aa49-27e17d57a28c
-- title:
--   Existence of a support-preserving rational shared-permutation sampler for the local conditional family
-- statement:
--   Assume the postselection mass is positive, and fix a base history flag $r_0$ and an accuracy $\gamma > 0$. Then there exist a denominator $m > 0$ and nonnegative integer numerators $N_k(r)$, indexed by local sampler indices $k$ (a remaining coordinate together with either an $X$-question or a $Y$-question) and history flags $r$, such that: (i) $\sum_r N_k(r) = m$ for every $k$, so each $r \mapsto N_k(r)/m$ is a probability distribution; (ii) each is within total variation distance $\gamma$ of the corresponding member of the local conditional family of the postselected source law with base $r_0$; (iii) the rounding preserves support, $N_k(r) > 0$ whenever that conditional is positive at $r$; and (iv) the associated shared-permutation sampler is both faithful and stable, namely a uniformly random permutation of $\mathcal{R} \times \{0,\dots,m-1\}$ outputs the letter $r$ with probability exactly $N_k(r)/m$ for each index $k$, and for any two indices the probability that the two outputs disagree is at most twice the total variation distance between $N_{\mathrm{left}}(\cdot)/m$ and $N_{\mathrm{right}}(\cdot)/m$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L51204-L51270

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exact_exists_support_preserving_local_shared_permutation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ∃ denominator : ℕ, 0 < denominator ∧
      ∃ numerator : ExactLocalSamplerIndex X Y D →
        ExactHistoryFlag X Y A B D → ℕ,
        (∀ index, (∑ history, numerator index history) = denominator) ∧
        (∀ index, finiteTotalVariation
          (exactLocalConditionalFamily D base
            (exactLocallySampleableLaw G n S D) index)
          (fun history =>
            (numerator index history : ℝ) / denominator) < gamma) ∧
        (∀ index history,
          0 < exactLocalConditionalFamily D base
              (exactLocallySampleableLaw G n S D)
              index history →
            0 < numerator index history) ∧
        ∃ nonempty : ∀ index,
          (rationalMarked denominator (numerator index)).Nonempty,
          (∀ index history,
            uniformPermutationProbability
              (fun permutation : Equiv.Perm
                (ExactHistoryFlag X Y A B D × Fin denominator) =>
                rationalPermutationOutput denominator (numerator index)
                  (nonempty index) permutation = history) =
                (numerator index history : ℝ) / denominator) ∧
          (∀ left right,
            uniformPermutationProbability
              (fun permutation : Equiv.Perm
                (ExactHistoryFlag X Y A B D × Fin denominator) =>
                rationalPermutationOutput denominator (numerator left)
                  (nonempty left) permutation ≠
                rationalPermutationOutput denominator (numerator right)
                  (nonempty right) permutation) ≤
              2 * finiteTotalVariation
                (fun history =>
                  (numerator left history : ℝ) / denominator)
                (fun history =>
                  (numerator right history : ℝ) / denominator)) := by sorry
