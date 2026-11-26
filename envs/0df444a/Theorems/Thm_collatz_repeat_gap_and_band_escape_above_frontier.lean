-- Prove2me | Theorems.Thm_collatz_repeat_gap_and_band_escape_above_frontier
-- name    : collatz_repeat_gap_and_band_escape_above_frontier
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:43:03.800968+00:00
-- url     : https://prove2.me/theorems/fb924c98-ca5c-5a43-a54c-b7672f326049
-- title:
--   Repeat gaps and band escape above the Collatz frontier floor
-- statement:
--   Let $C$ be the ordinary Collatz map, which sends even $x$ to $x/2$ and odd $x$ to $3x+1$. Let $n\ge 2310000$ and suppose $C^j(n)\ge n$ for every $j\ge 0$.
--
--   Prove both consequences for this orbit:
--   $$
--   C^a(n)=C^b(n),\quad a<b\quad\Longrightarrow\quad b-a\ge 14543,
--   $$
--   $$
--   \forall t\ge 0\;\exists j\in\{0,\ldots,14542\},\qquad C^{t+j}(n)\ge n+14542.
--   $$
--   The first is a lower bound on every repeat gap, including repeats in a tail. The second gives a value outside the corresponding band near $n$ in every window of the indicated length. The floor assumption holds on the unresolved branch whenever no smaller orbit meets the original.
-- source:
--   Auxiliary to https://prove2.me/theorems/6addc3e8-67b2-4e46-89d0-51db65db2c7b. Uses integer power comparisons for the classical Collatz cycle inequality; see Halbeisen and Hungerbühler, https://people.math.ethz.ch/~halorenz/publications/pdf/collatz.pdf.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_repeat_gap_and_band_escape_above_frontier (n : ℕ) (hlarge : 2310000≤n)
    (hstay : ∀ j : ℕ, n≤collatzStep^[j] n) :
    (∀ a b : ℕ, a<b → collatzStep^[a] n=collatzStep^[b] n → 14543≤b-a) ∧
    (∀ t : ℕ, ∃ j : ℕ, j≤14542 ∧ n+14542≤collatzStep^[t+j] n) := by
  sorry
