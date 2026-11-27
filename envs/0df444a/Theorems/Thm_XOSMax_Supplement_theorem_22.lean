-- Prove2me | Theorems.Thm_XOSMax_Supplement_theorem_22
-- name    : XOSMax.Supplement.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:38:46.034218+00:00
-- url     : https://prove2.me/theorems/4e6a41e3-6f6b-4063-abcf-9a7892944323
-- title:
--   Theorem 22 — at most $2^{O(k^2n^2)}$ order classes of $k$-XOS functions
-- statement:
--   There is an absolute constant $C>0$ such that, for every $k,n$, the number $N_{k,n}$ of order-equivalence classes of $k$-XOS functions on $[n]$ satisfies
--   $$
--   N_{k,n}\le2^{Ck^2n^2}.
--   $$
--   The constant is chosen before both parameters.
--
--   Differences from the source:
--   - encoding: the number of order-different real-valued functions → the number of comparison relations realized by $k$-XOS functions; reason: one realized relation is exactly one order-equivalence class, whereas counting functions would be uncountable
--   - encoding: $2^{O(k^2n^2)}$ → $2^{Ck^2n^2}$ for one positive natural $C$ uniform in $k,n$; reason: this is the quantified upper-bound meaning and the proof supplies an absolute constant
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 22, pp.13-14

import Mathlib
import Definitions.Def_XOSMax_Supplement_orderClassCount

namespace XOSMax.Supplement

/-- **Theorem 22.** The number of order-equivalence classes of `k`-XOS functions on `[n]` is at
most `2^(C k² n²)` for one absolute constant `C`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Theorem 22, pp.13–14).

**Formalization Note** The existential constant precedes both `k` and `n`. `orderClassCount`
counts realized comparison relations on the finite set of subsets, not the uncountable collection
of real-valued functions. -/
theorem theorem_22 :
    ∃ C : ℕ, 0 < C ∧ ∀ k n : ℕ,
      orderClassCount k n ≤ 2 ^ (C * k ^ 2 * n ^ 2) := by sorry

end XOSMax.Supplement
