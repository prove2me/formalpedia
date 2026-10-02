-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_hall_condition_of_regular_family
-- name    : ProofsInTheBook.Chapter33.hall_condition_of_regular_family
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:29.869319+00:00
-- url     : https://prove2.me/theorems/40bc0481-2411-404a-bfbf-6e3b6060c463
-- title:
--   Hall’s condition for a uniformly sized finite family
-- statement:
--   Let $I$ be a finite index set, let $X$ be a set, and assume decidable equality on both. Let $(A_i)_{i\in I}$ be finite subsets of $X$, and let $d\in\mathbb N$ satisfy $d>0$. Assume every $A_i$ has cardinality $d$ and every $x\in X$ belongs to at most $d$ sets. Then
--   $$\forall S\subseteq I,\qquad|S|\le\left|\bigcup_{i\in S}A_i\right|.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L76. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.hall_condition_of_regular_family {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (A : ι → Finset α) (d : ℕ)
    (hcard : ∀ i, (A i).card = d)
    (hfiber : ∀ a, ((Finset.univ : Finset ι).filter fun i => a ∈ A i).card ≤ d)
    (hd : 0 < d) :
    ∀ S : Finset ι, S.card ≤ (S.biUnion A).card := by sorry
