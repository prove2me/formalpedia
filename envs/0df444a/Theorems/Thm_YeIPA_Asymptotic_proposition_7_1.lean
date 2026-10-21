-- Prove2me | Theorems.Thm_YeIPA_Asymptotic_proposition_7_1
-- name    : YeIPA.Asymptotic.proposition_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:07.237679+00:00
-- url     : https://prove2.me/theorems/28cf0eb9-4c91-4b97-96ed-685ea610ffad
-- title:
--   Proposition 7.1 — the order of convergence of a positive null sequence equals liminf log r^{k+1} / log r^k
-- statement:
--   Let $\{r^k\}$ be a sequence of positive numbers converging to zero. Then its order of convergence (Definition 1.1: the supremum of the $p\ge0$ with $\limsup_k r^{k+1}/(r^k)^p<\infty$) equals
--   $$\liminf_{k\to\infty}\frac{\log r^{k+1}}{\log r^k}.$$
--
--   The proposition gives a closed form for the order of convergence, which the book uses to read off quadratic convergence of the duality gap.
--
--   **Formalization Note** Both sides are elements of `EReal` ($[-\infty,+\infty]$): the order of convergence may be $+\infty$ (for example for $r^k=\exp(-e^{e^k})$), and so may the limit inferior. The quotient $\log r^{k+1}/\log r^k$ is computed in $\mathbb R$; the finitely many $k$ with $r^k=1$, where Lean's convention gives the quotient $0$, do not affect the limit inferior because $r^k\to0$. The book leaves the proof as Exercise 7.1.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 210, Proposition 7.1

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_Order

namespace YeIPA.Asymptotic

/-- Proposition 7.1 (p. 210). Let the positive sequence `{rᵏ}` converge to zero. Then its order
of convergence (Definition 1.1) equals `liminf_{k→∞} log r^{k+1} / log r^k` (both in `EReal`). -/
theorem proposition_7_1 (r : ℕ → ℝ) (hpos : ∀ k, 0 < r k)
    (hlim : Filter.Tendsto r Filter.atTop (nhds 0)) :
    orderOfConvergence r =
      Filter.liminf (fun k => ((Real.log (r (k + 1)) / Real.log (r k) : ℝ) : EReal))
        Filter.atTop := by sorry

end YeIPA.Asymptotic
