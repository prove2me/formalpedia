-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_erdos_step1_n_gt_k_sq
-- name    : ProofsInTheBook.Chapter03.erdos_step1_n_gt_k_sq
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:35:41.240748+00:00
-- url     : https://prove2.me/theorems/2928940c-741e-4a3b-bbeb-feebaf683c61
-- title:
--   A hypothetical perfect power forces n above k squared
-- statement:
--   Let $n,k,\ell,m\in\mathbb N$ satisfy $k\ge4$, $2k\le n$, $\ell\ge2$, and $\binom nk=m^\ell$. Then
--   $$k^2<n.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L4092. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

lemma ProofsInTheBook.Chapter03.erdos_step1_n_gt_k_sq {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 2 ≤ l)
    (h_eq : n.choose k = m ^ l) : k * k < n := by sorry
