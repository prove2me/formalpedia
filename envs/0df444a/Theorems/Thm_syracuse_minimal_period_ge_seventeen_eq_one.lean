-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_seventeen_eq_one
-- name    : syracuse_minimal_period_ge_seventeen_eq_one
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:24:42.202652+00:00
-- url     : https://prove2.me/theorems/dbb30e5a-da29-4522-a4b6-055020fc4e5a
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least seventeen
-- statement:
--   Let $T$ denote the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m$ is a positive integer whose least positive return time under $T$ is $p$: that is, $T^p(m) = m$ and $T^k(m) \neq m$ for every $k$ with $0 < k < p$. Under the additional assumption $p \ge 17$, prove that $m = 1$.
--
--   Since $1$ has least period $1$, this would rule out the existence of such a cycle altogether.
--
--   This is the remaining open cycle obligation after least periods $1$ through $16$ have been excluded, and it replaces the earlier frontier at period $8$. The elementary margin method that settles all periods up to $16$ stops here: it needs the ratio $2^{K_a}/3^a$ (with $K_a$ least such that $3^a < 2^{K_a}$) to exceed $(103/34)^a/3^a$, and at $a = 17$ one has $2^{27}/3^{17} \approx 1.0393$ against $\approx 1.181$. Raising the numerical threshold on small cycle values buys only finitely much more ground — verifying that every odd value up to $147$ reaches $1$ would push the first gap from $17$ to $29$ — because $2^K/3^a$ comes arbitrarily close to $1$ along the convergents of $\log_2 3$. A uniform treatment of all large periods is a statement about linear forms in the logarithms of $2$ and $3$.
--
--   This is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split for syracuse_minimal_period_ge_eight_eq_one (efe4beff-fef3-4f9b-8d8d-1cf81a6649ca), using syracuse_period_le_sixteen_eq_one. Cf. Simons and de Weger, Theoretical and computational bounds for m-cycles of the 3n+1 problem, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_seventeen_eq_one (m p : ℕ) (hm : 0 < m) (hp : 17 ≤ p)
    (hcyc : syracuseStep^[p] m = m) (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    m = 1 := by sorry
