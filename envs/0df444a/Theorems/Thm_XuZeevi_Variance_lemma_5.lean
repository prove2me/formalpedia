-- Prove2me | Theorems.Thm_XuZeevi_Variance_lemma_5
-- name    : XuZeevi.Variance.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:07:40.4823+00:00
-- url     : https://prove2.me/theorems/4c874839-bc51-4d61-bbcb-8d6e2ff31969
-- title:
--   Lemma 5 — Talagrand concentration for empirical processes
-- statement:
--   Let $F$ be any class of measurable real functions on a probability space $(Z,P)$, with $B_1\le f(z)\le B_2$ for all $f\in F,z\in Z$, and $\operatorname{Var}_P f\le r$ for some $r>0$. Take an iid sample of size $n\ge1$ and $\delta\in(0,1)$. Assume the two signed deviation suprema and the empirical Rademacher complexity are measurable, as in p. 5. Write $RF=\mathbb E_S R_nF$, using independent fair signs with normalization $1/n$ and no absolute value inside the supremum.
--
--   Each of the following four statements has its own event of probability at least $1-\delta$:
--   $$\begin{aligned}
--   \forall f\in F:\quad Pf-P_nf&\le3RF+\sqrt{2r\log(1/\delta)/n}+(B_2-B_1)\log(1/\delta)/n,\\
--   \forall f\in F:\quad Pf-P_nf&\le4R_nF+\sqrt{2r\log(2/\delta)/n}+\tfrac92(B_2-B_1)\log(2/\delta)/n,\\
--   \forall f\in F:\quad P_nf-Pf&\le3RF+\sqrt{2r\log(1/\delta)/n}+(B_2-B_1)\log(1/\delta)/n,\\
--   \forall f\in F:\quad P_nf-Pf&\le4R_nF+\sqrt{2r\log(2/\delta)/n}+\tfrac92(B_2-B_1)\log(2/\delta)/n.
--   \end{aligned}$$
--   No simultaneous confidence for their intersection is claimed. The empty class is allowed and its uniform conclusions are vacuous; no assumption $0\in F$ or $f\ge0$ is added.
--
--   Differences from the source:
--   - encoding: n independent observations with law P → Fin n indexed sample under the product law, with 0 < n; reason: same joint distribution and normalization; the source divides by n
--   - encoding: with probability at least p → a measurable good event of measure at least ENNReal.ofReal p; reason: equivalent for the measurable events stipulated on p. 5; negative lower bounds impose no probability restriction
--   - encoding: supremum over F bounded above by a threshold → every f in F obeys that bound on the same event; reason: equivalent for nonempty bounded F and preserves the vacuous empty-class case without a real empty supremum
--   - encoding: measurable suprema convention of p. 5 → measurability of both signed deviation suprema and of empirical Rademacher complexity; reason: ensures genuine expectation and event probabilities without a pointwise-separable class restriction
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, Lemma 5, p. 58 (PDF p. 58); https://arxiv.org/abs/2011.06186v4

import Definitions.Def_XuZeevi_Variance_Sampling
import Definitions.Def_FoundationsML_RademacherVC_RademacherComplexity_v2

open MeasureTheory FoundationsML.RademacherVC

namespace XuZeevi.Variance

theorem lemma_5 {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [IsProbabilityMeasure P] (F : Set (Z → ℝ))
    (B₁ B₂ r δ : ℝ) (n : ℕ) (hn : 0 < n)
    (hr : 0 < r) (hδ : 0 < δ ∧ δ < 1)
    (hbounded : ∀ f ∈ F, ∀ z, B₁ ≤ f z ∧ f z ≤ B₂)
    (hmeas : ∀ f ∈ F, Measurable f)
    (hvar : ∀ f ∈ F, variance P f ≤ r)
    (hprocess : ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
      Measurable (fun s : Fin n → Z =>
        sSup ((fun f : Z → ℝ => sign * ((∫ z, f z ∂P) - empiricalMean s f)) '' F)))
    (hrad : Measurable (fun s : Fin n → Z => EmpiricalRademacherComplexity F s)) :
    (HighProbability (sampleLaw P n) (1 - δ) (fun s => ∀ f ∈ F,
      (∫ z, f z ∂P) - empiricalMean s f ≤
        3 * RademacherComplexity P F n + Real.sqrt (2 * r * Real.log (1 / δ) / n) +
          (B₂ - B₁) * Real.log (1 / δ) / n)) ∧
    (HighProbability (sampleLaw P n) (1 - δ) (fun s => ∀ f ∈ F,
      (∫ z, f z ∂P) - empiricalMean s f ≤
        4 * EmpiricalRademacherComplexity F s + Real.sqrt (2 * r * Real.log (2 / δ) / n) +
          (9 / 2 : ℝ) * (B₂ - B₁) * Real.log (2 / δ) / n)) ∧
    (HighProbability (sampleLaw P n) (1 - δ) (fun s => ∀ f ∈ F,
      empiricalMean s f - (∫ z, f z ∂P) ≤
        3 * RademacherComplexity P F n + Real.sqrt (2 * r * Real.log (1 / δ) / n) +
          (B₂ - B₁) * Real.log (1 / δ) / n)) ∧
    (HighProbability (sampleLaw P n) (1 - δ) (fun s => ∀ f ∈ F,
      empiricalMean s f - (∫ z, f z ∂P) ≤
        4 * EmpiricalRademacherComplexity F s + Real.sqrt (2 * r * Real.log (2 / δ) / n) +
          (9 / 2 : ℝ) * (B₂ - B₁) * Real.log (2 / δ) / n)) := by sorry

end XuZeevi.Variance
