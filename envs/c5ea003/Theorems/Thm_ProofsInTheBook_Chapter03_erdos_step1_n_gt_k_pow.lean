-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_erdos_step1_n_gt_k_pow
-- name    : ProofsInTheBook.Chapter03.erdos_step1_n_gt_k_pow
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:35:35.466982+00:00
-- url     : https://prove2.me/theorems/9f681458-6591-4058-9116-12d9af05e59b
-- title:
--   A hypothetical perfect power forces n above k to that exponent
-- statement:
--   Let $n,k,\ell,m\in\mathbb N$ satisfy $k\ge4$, $2k\le n$, $\ell\ge2$, and $\binom nk=m^\ell$. Then
--   $$k^\ell<n.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L4124. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

lemma ProofsInTheBook.Chapter03.erdos_step1_n_gt_k_pow {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n)
    (hl : 2 ≤ l) (h_eq : n.choose k = m ^ l) : k ^ l < n := by sorry
