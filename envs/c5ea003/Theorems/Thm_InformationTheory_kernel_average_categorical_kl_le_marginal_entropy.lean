-- Prove2me | Theorems.Thm_InformationTheory_kernel_average_categorical_kl_le_marginal_entropy
-- name    : InformationTheory.kernel_average_categorical_kl_le_marginal_entropy
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T00:14:00.212088+00:00
-- url     : https://prove2.me/theorems/71d53657-1c19-4629-a0a9-42aef819d2af
-- title:
--   Average categorical KL divergence is bounded by marginal entropy
-- statement:
--   Let $\mu$ be a probability measure on a standard Borel space $\mathcal X$, and let $\kappa(\cdot\mid x)$ be a Markov kernel from $\mathcal X$ to a finite action set $[k]$. Write $p=\mu\kappa$ for the marginal action distribution. Then
--
--   $$
--   \int_{\mathcal X} D\!\left(\kappa(\cdot\mid x)\,\middle\|\,p\right)\,\mu(dx)
--   \;\le\;
--   H(p)
--   =\sum_{a\in[k]}-p(a)\log p(a).
--   $$
--
--   Thus the expected information carried by a finite-valued conditional distribution is no larger than the entropy of its marginal. This is the entropy bound used in the information-ratio proof of the Bayesian Thompson-sampling regret theorem.
--
--   **Formalization Note** The conclusion is stated for real-valued KL divergence and uses `negMulLog` so that zero-probability atoms are handled continuously.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), printed pp. 470–471, Theorem 36.6 and Lemma 36.7, https://tor-lattimore.com/downloads/book/book.pdf; abstracted entropy step in the proof.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators

namespace InformationTheory

theorem kernel_average_categorical_kl_le_marginal_entropy
    {Alpha : Type} {mAlpha : MeasurableSpace Alpha}
    [StandardBorelSpace Alpha] [Nonempty Alpha]
    {k : ℕ} [NeZero k] (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (kappa : Kernel Alpha (Fin k)) [IsMarkovKernel kappa] :
    ∫ x, (klDiv (kappa x) (kappa ∘ₘ mu)).toReal ∂mu ≤
      ∑ a, Real.negMulLog ((kappa ∘ₘ mu).real {a}) := by
  sorry

end InformationTheory
