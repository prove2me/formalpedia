-- Prove2me | Theorems.Thm_InformationTheory_kernel_average_categorical_kl_le_marginal_entropy_general
-- name    : InformationTheory.kernel_average_categorical_kl_le_marginal_entropy_general
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T00:25:20.07343+00:00
-- url     : https://prove2.me/theorems/289e87f9-6c92-4857-8357-1633812c968d
-- title:
--   Average finite-valued KL divergence is bounded by marginal entropy
-- statement:
--   Let $\mu$ be a probability measure on an arbitrary measurable space $\mathcal X$, and let $\kappa(\cdot\mid x)$ be a Markov kernel from $\mathcal X$ to a finite action set $[k]$. Write $p=\mu\kappa$ for the marginal action distribution. Then
--
--   $$
--   \int_{\mathcal X} D\!\left(\kappa(\cdot\mid x)\,\middle\|\,p\right)\,\mu(dx)
--   \;\le\;
--   H(p)
--   =\sum_{a\in[k]}-p(a)\log p(a).
--   $$
--
--   No topological or standard-Borel assumption is needed on $\mathcal X$: finiteness of the output alphabet suffices. This general form is the entropy bound used when a joint law is disintegrated into a finite-valued conditional distribution.
--
--   **Formalization Note** The proof derives almost-everywhere absolute continuity directly from $p(a)=\int\kappa(a\mid x)\,\mu(dx)$, so it does not rely on a posterior-kernel construction on the source space.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), printed pp. 470–471, Theorem 36.6 and Lemma 36.7, https://tor-lattimore.com/downloads/book/book.pdf; abstracted finite-alphabet entropy step.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators

namespace InformationTheory

theorem kernel_average_categorical_kl_le_marginal_entropy_general
    {Alpha : Type} {mAlpha : MeasurableSpace Alpha}
    {k : ℕ} [NeZero k] (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (kappa : Kernel Alpha (Fin k)) [IsMarkovKernel kappa] :
    ∫ x, (klDiv (kappa x) (kappa ∘ₘ mu)).toReal ∂mu ≤
      ∑ a, Real.negMulLog ((kappa ∘ₘ mu).real {a}) := by
  sorry

end InformationTheory
