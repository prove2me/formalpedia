-- Prove2me | Theorems.Thm_XOSMax_Supplement_theorem_23
-- name    : XOSMax.Supplement.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:39:29.578503+00:00
-- url     : https://prove2.me/theorems/cbda614c-72db-475a-ad69-b5855ad29e4e
-- title:
--   Theorem 23 — at least $2^{\Omega(n^2)}$ additive order classes
-- statement:
--   There are $c>0$ and $N$ such that, for every $n\ge N$, the number $N_{1,n}$ of order-equivalence classes of additive, equivalently $1$-XOS, functions on $[n]$ satisfies
--   $$
--   N_{1,n}\ge2^{cn^2}.
--   $$
--   Additivity is normalized through the paper's signed one-clause XOS representation.
--
--   Differences from the source:
--   - encoding: the number of order-different additive functions → the number of comparison relations realized by `IsKXOS 1`; reason: these relations are exactly the order-equivalence classes and `IsKXOS 1` is the paper's normalized additive class
--   - encoding: $2^{\Omega(n^2)}$ → $2^{cn^2}$ for positive real $c$ after a threshold $N$; reason: this is the quantified lower-bound meaning without truncating the exponent
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 23, p.14

import Mathlib
import Definitions.Def_XOSMax_Supplement_orderClassCount

namespace XOSMax.Supplement

/-- **Theorem 23.** The number of order-equivalence classes of additive (`1`-XOS) functions on
`[n]` is at least `2^(c n²)` for all sufficiently large `n`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Theorem 23, p.14).

**Formalization Note** Additivity is the published normalized `IsKXOS 1` notion. A positive real
constant and an explicit asymptotic threshold unpack `2^Ω(n²)` without truncating its exponent. -/
theorem theorem_23 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.rpow 2 (c * (n : ℝ) ^ 2) ≤ orderClassCount 1 n := by sorry

end XOSMax.Supplement
