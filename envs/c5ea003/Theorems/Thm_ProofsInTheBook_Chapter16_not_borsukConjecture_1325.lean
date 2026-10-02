-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter16_not_borsukConjecture_1325
-- name    : ProofsInTheBook.Chapter16.not_borsukConjecture_1325
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T15:18:03.407323+00:00
-- url     : https://prove2.me/theorems/90bcee74-f95e-47db-97d2-e5d1a5018041
-- title:
--   Borsuk’s conjecture fails in dimension 1325
-- statement:
--   There exists a bounded set $S\subseteq\mathbb R^{1325}$ with $\operatorname{diam}(S)>0$ for which there is no family $A_1,\ldots,A_{1326}$ satisfying
--   $$S\subseteq\bigcup_{i=1}^{1326}A_i,\qquad A_i\subseteq S,\qquad \operatorname{diam}(A_i)<\operatorname{diam}(S)\quad\text{for every }i.$$
--   The diameter and distance are Euclidean. The covering subsets need not be disjoint. The statement has no external counterexample or combinatorial-certificate hypothesis.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 18, “Borsuk’s conjecture”, pp. 117–123 (https://doi.org/10.1007/978-3-662-57265-8_18). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter16.lean#L2586. The book citation identifies the topic; the selected declaration does not claim to reproduce the entire chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter16
open ProofsInTheBook.Chapter16

theorem ProofsInTheBook.Chapter16.not_borsukConjecture_1325 : ¬ BorsukConjecture 1325 := by sorry
