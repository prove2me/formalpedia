-- Prove2me | Theorems.Thm_XOSMax_Supplement_theorem_2
-- name    : XOSMax.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:34:55.137987+00:00
-- url     : https://prove2.me/theorems/545eeaa0-169d-46e5-9bd2-4372280b4df6
-- title:
--   Theorem 2 — randomized $\max(1,\varepsilon n/\log n)$-approximation
-- statement:
--   For every $\varepsilon>0$ there is $C>0$ such that one randomized value-oracle algorithm, fixed before the input function, satisfies
--   $$
--   \mathbb E[f(\widetilde X)]\ge\frac{1}{\max\{1,\varepsilon n/\log n\}}\max_{X\subseteq V}f(X)
--   $$
--   for every XOS function. For $n\ge2$, every run in its support makes at most $C n^{1/\varepsilon+1}\log n$ oracle calls.
--
--   Differences from the source:
--   - encoding: an $(\varepsilon n/\log n)$-approximation → a $\max(1,\varepsilon n/\log n)$-approximation; reason: ratios are defined only for $\alpha\ge1$, and the source's bounded-small-$n$ branch is exact
--   - encoding: randomized algorithm and expected value → a probability mass function on terminating oracle programs and its weighted sum; reason: randomness is independent of $f$ and this is the literal expectation
--   - encoding: $O(n^{1/\varepsilon+1}\log n)$ time → the bound for $n\ge2$ on every supported run's query count; reason: the source counts oracle calls, and asymptotic notation does not impose the zero right-hand side at $n=1$
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 2, p.2; Algorithm 2 and Claim 7, pp.4-5

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_OracleProg
import Definitions.Def_XOSMax_Supplement_RandomizedProg

namespace XOSMax.Supplement

open XOSMax OracleProg

/-- **Theorem 2.** For every `ε > 0`, a randomized value-oracle algorithm has expected
approximation ratio `max(1, εn/log n)` and uses `O(n^(1/ε+1) log n)` oracle calls
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Theorem 2, p.2).

**Formalization Note** The distribution on programs is chosen before `f`; its expectation is the
paper's definition of randomized approximation. The query bound holds on every random program in
the support and is stated for `n ≥ 2`, where `log n > 0`. The exact small-instance branch is captured
by `max 1`; the constant depends on `ε` only. -/
theorem theorem_2 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (L : List E),
        L.Nodup → L.toFinset = Finset.univ →
        ∃ A : RandomizedProg E (Finset E), ∀ f : Finset E → ℝ,
          (∃ k : ℕ, IsKXOS k f) →
          (∀ X : Finset E, (1 / max 1
              (ε * Fintype.card E / Real.log (Fintype.card E))) * f X ≤ expectedValue A f) ∧
          (2 ≤ Fintype.card E → ∀ p ∈ A.support,
            (queries f p : ℝ) ≤ C * Real.rpow (Fintype.card E) (1 / ε + 1) *
              Real.log (Fintype.card E)) := by sorry

end XOSMax.Supplement
