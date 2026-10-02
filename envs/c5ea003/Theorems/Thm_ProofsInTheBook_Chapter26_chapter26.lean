-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter26_chapter26
-- name    : ProofsInTheBook.Chapter26.chapter26
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:11:13.805165+00:00
-- url     : https://prove2.me/theorems/998e25c7-7ca3-4479-951f-75cb295aff99
-- title:
--   Erdős–Szekeres monotone subsequence theorem
-- statement:
--   Let $n\in\mathbb N$ and let $a:\operatorname{Fin}(n^2+1)\to\mathbb R$ be injective. There exists a subset $T$ of indices with
--   $$|T|\ge n+1$$
--   such that either $a_i<a_j$ for every $i<j$ in $T$, or $a_i>a_j$ for every $i<j$ in $T$.
--
--   Thus every sequence of $n^2+1$ distinct real numbers contains a strictly increasing or strictly decreasing subsequence of at least $n+1$ terms.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 28, “Pigeon-hole and double counting”, pp. 195–205 (https://doi.org/10.1007/978-3-662-57265-8_28). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter26.lean#L227. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter26
open Finset Function
open ProofsInTheBook.Chapter26

theorem ProofsInTheBook.Chapter26.chapter26 (n : ℕ) {a : Fin (n ^ 2 + 1) → ℝ} (ha : Injective a) :
    (∃ t : Finset (Fin (n ^ 2 + 1)), n + 1 ≤ t.card ∧ StrictMonoOn a ↑t) ∨
    (∃ t : Finset (Fin (n ^ 2 + 1)), n + 1 ≤ t.card ∧ StrictAntiOn a ↑t) := by sorry
