-- Prove2me | Theorems.Thm_ProofsInTheBook_PlanarMap_CombMap_alpha_class_card
-- name    : ProofsInTheBook.PlanarMap.CombMap.alpha_class_card
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:24:21.846057+00:00
-- url     : https://prove2.me/theorems/583d07cd-8548-4b2a-9f89-2f058ea4a847
-- title:
--   Every edge orbit contains two darts
-- statement:
--   Let D be a finite set of darts (with decidable equality in the formalization). A combinatorial map M consists of permutations $\alpha,\sigma$ of D, with $\alpha^2=1$ and $\alpha(d)\ne d$ for all darts. Put $\varphi=\sigma\circ\alpha$; the numbers V,E,F count the orbits of $\sigma,\alpha,\varphi$, respectively. For every orbit Q of $\alpha$,
--   $$|\{d\in D:[d]_\alpha=Q\}|=2.$$
--   No connectivity, Euler-characteristic, or regular-degree condition is assumed.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L106. Topic reference: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 13, “Three applications of Euler’s formula”, pp. 89–94 (https://doi.org/10.1007/978-3-662-57265-8_13). The citation identifies the topic; the formal statement uses the specified combinatorial-map model.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter12
open ProofsInTheBook.PlanarMap
open Equiv
open ProofsInTheBook.PlanarMap.CombMap
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma ProofsInTheBook.PlanarMap.CombMap.alpha_class_card (M : CombMap D)
    (q : Quotient (cycleSetoid M.α)) :
    (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.α) x = q)).card = 2 := by sorry
