-- Prove2me | Theorems.Thm_ZeroExtensionGap_theorem_4_retraction
-- name    : ZeroExtensionGap.theorem_4_retraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:01:19.599108+00:00
-- url     : https://prove2.me/theorems/f2e1611e-5310-4e4e-8aa6-5002f6c9e5cf
-- title:
--   Theorem 4 ([LS09], cited) — random retractions from random partitions
-- statement:
--   Let $(M,d)$ be a finite metric space, let $B\subseteq M$ be nonempty, and let $\beta\ge0$. Suppose that for every $\Lambda>0$ there is a $\Lambda$-bounded random partition $Q_\Lambda$ of $M$ with $\Pr[Q_\Lambda(x)\ne Q_\Lambda(y)]\le\beta\,d(x,y)/\Lambda$ for every $x,y\in M$. Then there is a random retraction $g:M\to B$ such that $d(x,g(x))\le5\,d(x,B)$ for every $x\in M$, and for every $x,y\in M\setminus B$,
--
--   $$\Pr[g(x)\ne g(y)]\le(\beta+2)\frac{d(x,y)}{\min\{d(x,B),d(y,B)\}}.$$
--
--   This result of Lee and Sidiropoulos is cited.
--
--   Differences from the source:
--   - encoding: a random partition → its law, `PMF (Finpartition _)`; reason: partitions of a finite set form a finite type, whatever process generated them
--   - encoding: a random retraction $g:M\to B$; $d(x,B)=\min_{b\in B}d(x,b)$ → a `PMF (M → M)` whose support consists of retractions; `Metric.infDist`; reason: $M$ is finite, so the law carries the same events and the infimum over the nonempty finite $B$ is the minimum
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Theorem 4, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_ZeroExtensionGap_RandomPartition

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Theorem 4 ([LS09]), p.23 (PDF p.25). A cited result.
**Formalization Note.** `d(x, B)` is `Metric.infDist x B`, the minimum over the nonempty finite `B`, which is
positive for `x ∉ B`. A random retraction is the law `g` of a map `M → M` whose every outcome is a retraction
onto `B` with `d(x, h(x)) ≤ 5 d(x, B)` for all `x`. -/
theorem theorem_4_retraction {M : Type*} [MetricSpace M] [Fintype M] [DecidableEq M]
    (B : Finset M) (hB : B.Nonempty) (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ Λ : ℝ, 0 < Λ → ∃ Q : PMF (Finpartition (Finset.univ : Finset M)),
      IsBoundedRandomPartition (fun x y => ENNReal.ofReal (dist x y)) Λ Q ∧
      ∀ x y : M, separationProb Q x y ≤ β * dist x y / Λ) :
    ∃ g : PMF (M → M),
      (∀ h ∈ g.support, IsRetractionOnto B h ∧
        ∀ x, dist x (h x) ≤ 5 * Metric.infDist x (B : Set M)) ∧
      ∀ x y : M, x ∉ B → y ∉ B →
        (g.toOuterMeasure {h | h x ≠ h y}).toReal ≤
          (β + 2) * dist x y / min (Metric.infDist x (B : Set M)) (Metric.infDist y (B : Set M)) := by sorry

end ZeroExtensionGap
