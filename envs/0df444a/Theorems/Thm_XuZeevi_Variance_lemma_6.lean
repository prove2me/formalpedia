-- Prove2me | Theorems.Thm_XuZeevi_Variance_lemma_6
-- name    : XuZeevi.Variance.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:07:34.269419+00:00
-- url     : https://prove2.me/theorems/582f4fc9-ec53-488e-bb97-24398e5ce1b4
-- title:
--   Lemma 6 — Bernstein inequality under averaged moment bounds
-- statement:
--   Let $X_1,\ldots,X_n$, $n\ge1$, be independent measurable mean-zero real random variables on any probability space. They need not be identically distributed or bounded. Let $\sigma,B>0$, and suppose that for every integer $k\ge2$ their absolute $k$th moments are finite and
--   $$\frac1n\sum_{i=1}^n\mathbb E|X_i|^k\le\frac{k!}{2}\sigma^2B^{k-2}.$$
--   For each $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$\left|\frac1n\sum_{i=1}^nX_i\right|\le\sqrt{\frac{2\sigma^2\log(2/\delta)}n}+\frac{B\log(2/\delta)}n.$$
--   The moment bound is averaged across the independent variables, not imposed separately on each, and applies to all $k\ge2$. Finiteness of the second moments also ensures the means are genuine integrals.
--
--   Differences from the source:
--   - encoding: X1 through Xn, with n in the denominator → Fin n indexed random variables with 0 < n; reason: preserves the sample and excludes only the undefined empty average
--   - encoding: with probability at least p → a measurable good event of measure at least ENNReal.ofReal p; reason: equivalent for the measurable events stipulated on p. 5; negative lower bounds impose no probability restriction
--   - encoding: finite upper bounds on absolute moments → Integrable for every absolute kth power, together with the averaged real-integral inequality; reason: nonnegative moments with a finite averaged upper bound are individually finite; avoids Bochner-integral defaults
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, Lemma 6, p. 58 (PDF p. 58); https://arxiv.org/abs/2011.06186v4

import Definitions.Def_XuZeevi_Variance_Sampling

open MeasureTheory ProbabilityTheory

namespace XuZeevi.Variance

theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (σ B δ : ℝ) (hσ : 0 < σ) (hB : 0 < B) (hδ : 0 < δ ∧ δ < 1)
    (hmom : ∀ k : ℕ, 2 ≤ k →
      (∀ i, Integrable (fun ω => |X i ω| ^ k) P) ∧
      (1 / (n : ℝ)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ k ∂P) ≤
        ((Nat.factorial k : ℝ) / 2) * σ ^ 2 * B ^ (k - 2)) :
    HighProbability P (1 - δ) (fun ω =>
      |(1 / (n : ℝ)) * ∑ i : Fin n, X i ω| ≤
        Real.sqrt (2 * σ ^ 2 * Real.log (2 / δ) / n) + B * Real.log (2 / δ) / n) := by sorry

end XuZeevi.Variance
