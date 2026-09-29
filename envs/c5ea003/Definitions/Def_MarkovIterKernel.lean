-- Prove2me | Definitions.Def_MarkovIterKernel
-- name    : MarkovIterKernel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-15T14:35:23.872225+00:00
-- url     : https://prove2.me/theorems/d6cac832-b28c-4343-873e-13f2bc29f7b4
-- title:
--   The $n$-step transition kernel $P^n$
-- statement:
--   The $n$-step transition kernel $P^n$ of a transition kernel $P$ on a measurable space $\mathsf{X}$, defined inductively: $P^0(x, \cdot)$ is the point mass at $x$, and
--
--   $$
--   P^{n+1}(x, A) \;=\; \int_{\mathsf{X}} P(y, A) \, P^n(x, dy)
--   $$
--
--   for every $x \in \mathsf{X}$ and measurable $A \subseteq \mathsf{X}$.
--
--   All ergodicity and minorization notions of the mission are phrased in terms of $P^n$; the definition is generic and reusable for any kernel.
--
--   **Formalization Note** If $P$ is a Markov (probability) kernel then so is every $P^n$; this instance is provided with the definition.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2 (arXiv v2 p. 3), the n-step kernel P^n(x, dy)

import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Comp

/-!
The `n`-step transition kernel of a Markov kernel.

Source: Galin L. Jones, *On the Markov Chain Central Limit Theorem*,
Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), §2: the `n`-step
kernel `Pⁿ(x, dy)`.
-/

open ProbabilityTheory

namespace MarkovChainCLT

/-- The `n`-step transition kernel `Pⁿ` of a Markov transition kernel `P`:
`iterKernel P 0` is the identity (Dirac) kernel and
`iterKernel P (n+1) = P ∘ₖ iterKernel P n`. -/
noncomputable def iterKernel {X : Type*} [MeasurableSpace X] (P : Kernel X X) :
    ℕ → Kernel X X
  | 0 => Kernel.id
  | n + 1 => P ∘ₖ iterKernel P n

@[simp] lemma iterKernel_zero {X : Type*} [MeasurableSpace X] (P : Kernel X X) :
    iterKernel P 0 = Kernel.id := rfl

@[simp] lemma iterKernel_succ {X : Type*} [MeasurableSpace X] (P : Kernel X X) (n : ℕ) :
    iterKernel P (n + 1) = P ∘ₖ iterKernel P n := rfl

instance iterKernel.instIsMarkovKernel {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) : IsMarkovKernel (iterKernel P n) := by
  induction n with
  | zero => rw [iterKernel_zero]; infer_instance
  | succ n ih => rw [iterKernel_succ]; exact Kernel.IsMarkovKernel.comp _ _

end MarkovChainCLT


