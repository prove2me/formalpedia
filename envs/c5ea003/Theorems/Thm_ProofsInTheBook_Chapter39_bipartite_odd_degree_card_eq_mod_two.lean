-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_bipartite_odd_degree_card_eq_mod_two
-- name    : ProofsInTheBook.Chapter39.bipartite_odd_degree_card_eq_mod_two
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:58.530776+00:00
-- url     : https://prove2.me/theorems/4669111a-4021-4f28-a0fc-317f260ef6f4
-- title:
--   Parity agreement for odd-degree vertices in a finite bipartite graph
-- statement:
--   Let $R,S$ be finite sets and let $E\subseteq R\times S$ be a decidable incidence relation. Define $\deg_R(r)=|\{s\in S:(r,s)\in E\}|$ and $\deg_S(s)=|\{r\in R:(r,s)\in E\}|$. Then
--   $$|\{r\in R:\deg_R(r)\text{ is odd}\}|\equiv|\{s\in S:\deg_S(s)\text{ is odd}\}|\pmod 2.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L2292. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.bipartite_odd_degree_card_eq_mod_two
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge] :
    (Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} : ZMod 2) =
      (Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} : ZMod 2) := by sorry
