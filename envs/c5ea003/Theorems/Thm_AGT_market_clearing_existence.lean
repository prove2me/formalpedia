-- Prove2me | Theorems.Thm_AGT_market_clearing_existence
-- name    : AGT.market_clearing_existence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:15:24.235948+00:00
-- url     : https://prove2.me/theorems/fd9131df-0780-4e7c-b6b1-c791175585e8
-- title:
--   Market-clearing prices exist in the linear 0/1 market
-- statement:
--   Market-clearing prices exist in the linear market with 0/1 utilities. The market (§1.8.1 of *Algorithmic Game Theory*): a finite set $A$ of divisible goods, good $a$ available in $s_a \ge 1$ units; a finite set $B$ of buyers, buyer $j$ bringing budget $m_j > 0$ and interested in a nonempty set $\Gamma_j \subseteq A$ of goods; every good interests at least one buyer; a buyer values any goods from her interest set equally and everything else not at all. Then there are prices $p_a > 0$ and spending amounts $x_{ja} \ge 0$ (money spent by buyer $j$ on good $a$) such that
--
--   1. $x_{ja} \ne 0$ only when $a \in \Gamma_j$ and $p_a = \min_{b \in \Gamma_j} p_b$ — each buyer spends only on cheapest goods in her interest set, an optimal bundle for 0/1 utilities;
--   2. $\sum_a x_{ja} = m_j$ for every buyer $j$ — budgets are exactly exhausted;
--   3. $\sum_j x_{ja} = p_a \, s_a$ for every good $a$ — every good sells out exactly.
--
--   This is the existence content of Theorem 1.17 of the book.
--
--   *A note on the rendering.* The book's Theorem 1.17 asserts that the ascending tight-set algorithm of §1.8.1 (via Lemmas 1.15–1.16 and max-flow) computes such prices in polynomial time; the running-time half is a statement about an algorithm and has no formal counterpart here, so this milestone is the existence content. Allocations are recorded as money spent rather than quantity, so the clearing condition is a product, not a quotient — no division by prices occurs anywhere in the statement.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 1.8.1, Lemmas 1.15-1.16 and Theorem 1.17, pp. 22-26 (existence form)

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

namespace AGT

/-- **Theorem 1.17 of *Algorithmic Game Theory* (existence form)**.  The
market of §1.8.1: finitely many divisible goods `A`, good `a` available in
`supply a` units; finitely many buyers `B`, buyer `j` bringing `money j` and
interested in the goods `interest j`.  Utilities are linear 0/1: a buyer
only values (any amount of) the goods she is interested in.

Conclusion: market-clearing prices and an allocation exist.  `spend j a` is
the money buyer `j` spends on good `a`; each buyer spends her entire budget,
spends it only on interested goods of minimum price among her interest set
(an optimal bundle for 0/1 utilities), and every good sells out exactly —
total spending on `a` equals `price a * supply a`.

The book proves this by the iterated tight-set/max-flow algorithm
(Lemmas 1.15–1.16) and additionally shows polynomial running time; the
algorithmic half has no formal counterpart here.  Hypotheses: every buyer is
interested in at least one good and every good interests at least one buyer,
exactly the standing assumptions of §1.8.1; positive supplies and budgets
rule out degenerate zero prices. -/
theorem market_clearing_existence {A B : Type*} [Fintype A] [Fintype B]
    (supply : A → ℕ) (hsupply : ∀ a, 0 < supply a)
    (money : B → ℝ) (hmoney : ∀ j, 0 < money j)
    (interest : B → Finset A) (hbuyer : ∀ j, (interest j).Nonempty)
    (hgood : ∀ a : A, ∃ j : B, a ∈ interest j) :
    ∃ (price : A → ℝ) (spend : B → A → ℝ),
      (∀ a, 0 < price a) ∧
      (∀ j a, 0 ≤ spend j a) ∧
      (∀ j a, spend j a ≠ 0 →
        a ∈ interest j ∧ ∀ b ∈ interest j, price a ≤ price b) ∧
      (∀ j, ∑ a, spend j a = money j) ∧
      (∀ a, ∑ j, spend j a = price a * (supply a : ℝ)) := by
  sorry

end AGT
