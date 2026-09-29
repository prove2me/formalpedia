-- Prove2me | Theorems.Thm_InformationTheory_compProd_categorical_kl_le_marginal_entropy_general
-- name    : InformationTheory.compProd_categorical_kl_le_marginal_entropy_general
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T00:25:53.479328+00:00
-- url     : https://prove2.me/theorems/0a6f9a0f-ba27-4541-9e99-3b80cc567bf0
-- title:
--   Finite-valued conditional KL is bounded by marginal entropy
-- statement:
--   Let $\mu$ be a probability measure on an arbitrary measurable space $\mathcal X$, let $\kappa$ be a Markov kernel from $\mathcal X$ to a finite action set $[k]$, and put $p=\mu\kappa$. Then
--
--   $$
--   D\!\left(\mu\otimes\kappa\,\middle\|\,\mu\otimes p\right)
--   \;\le\;
--   H(p)
--   =\sum_{a\in[k]}-p(a)\log p(a).
--   $$
--
--   This is the conditional-kernel form of the fact that information carried by a finite-valued variable is bounded by its entropy. The source measurable space needs no regularity beyond what is required to define the kernel.
--
--   **Formalization Note** The independent coupling $\mu\otimes p$ is represented by a composition-product with a constant kernel.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), printed pp. 470–471, Theorem 36.6 and Lemma 36.7, https://tor-lattimore.com/downloads/book/book.pdf; conditional-kernel form of the finite-alphabet entropy step.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace InformationTheory

theorem compProd_categorical_kl_le_marginal_entropy_general
    {Alpha : Type} {mAlpha : MeasurableSpace Alpha}
    {k : ℕ} [NeZero k] (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (kappa : Kernel Alpha (Fin k)) [IsMarkovKernel kappa] :
    (klDiv (mu ⊗ₘ kappa)
      (mu ⊗ₘ Kernel.const Alpha (kappa ∘ₘ mu))).toReal ≤
      ∑ a, Real.negMulLog ((kappa ∘ₘ mu).real {a}) := by
  sorry

end InformationTheory
