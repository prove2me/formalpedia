-- Prove2me | Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
-- name    : InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T17:01:13.911111+00:00
-- url     : https://prove2.me/theorems/ae1b5db9-0972-42b5-a34e-cc836c098771
-- title:
--   Conditional relative entropy as an average, under a.e. absolute continuity
-- statement:
--   The conditional relative entropy of two composition-products equals the average of the fibrewise divergences, assuming absolute continuity of the fibres only *almost everywhere*.
--
--   Let $\mu$ be a finite measure on $(\mathcal A,\mathcal F)$ and $\kappa,\eta$ finite kernels from $\mathcal A$ to $(\mathcal B,\mathcal G)$ with $\kappa_a\ll\eta_a$ for $\mu$-almost every $a$. Then
--
--   $$
--   D\big(\mu\otimes\kappa \,\big\Vert\, \mu\otimes\eta\big) \;=\; \int_{\mathcal A} D\big(\kappa_a\,\Vert\,\eta_a\big)\,\mathrm d\mu(a).
--   $$
--
--   Weakening the hypothesis from "for every $a$" to "for $\mu$-almost every $a$" is what makes the identity usable in the situations it is meant for. A typical example: a learner whose action distribution never selects a particular arm on some event. Off that event the corresponding fibres need not be absolutely continuous at all — the fibrewise divergence may be genuinely infinite — yet the identity still holds, because those fibres are invisible to $\mu$. Requiring absolute continuity everywhere would exclude exactly the cases where the conclusion is most useful.
--
--   **Formalization Note** Both sides are unchanged when the kernels are modified on a $\mu$-null set, since the composition-product depends on the kernel only up to $\mu$-almost-everywhere equality; this is what allows the everywhere-hypothesis in the companion statement to be relaxed.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Exercise 14.12 (Chain rule), printed p. 196, where the conditional term is an expectation of divergences between regular conditional distributions, and only the almost-everywhere behaviour of those conditionals matters.

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.RadonNikodym

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

theorem InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  sorry
