-- Prove2me | Theorems.Thm_ProofsInTheBook_PlanarMap_CombMap_platonic_constraint
-- name    : ProofsInTheBook.PlanarMap.CombMap.platonic_constraint
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:24:29.907232+00:00
-- url     : https://prove2.me/theorems/dd93f61a-3655-4c46-8045-762d9893e721
-- title:
--   The degree inequality for a regular sphere map
-- statement:
--   Let D be a finite set of darts (with decidable equality in the formalization). A combinatorial map M consists of permutations $\alpha,\sigma$ of D, with $\alpha^2=1$ and $\alpha(d)\ne d$ for all darts. Put $\varphi=\sigma\circ\alpha$; the numbers V,E,F count the orbits of $\sigma,\alpha,\varphi$, respectively. Assume M is connected: any two darts can be joined by steps within one $\sigma$-orbit or across an $\alpha$-pair. Assume also $V-E+F=2$ (integer arithmetic). Let p,q be natural numbers, and assume every $\varphi$-orbit has exactly p darts and every $\sigma$-orbit has exactly q darts. If $p>0$, $q>0$, and $E>0$, then
--   $$pq<2p+2q.$$
--   The positive-degree premises here are weaker than the p,q>=3 premises in the five-pair classification.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L174. Topic reference: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 13, “Three applications of Euler’s formula”, pp. 89–94 (https://doi.org/10.1007/978-3-662-57265-8_13). The citation identifies the topic; the formal statement uses the specified combinatorial-map model.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter12
open ProofsInTheBook.PlanarMap
open Equiv
open ProofsInTheBook.PlanarMap.CombMap
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem ProofsInTheBook.PlanarMap.CombMap.platonic_constraint (M : CombMap D) (hsphere : M.IsSphereMap)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hE : 0 < M.E)
    (hF : M.FaceRegular p) (hV : M.VertexRegular q) :
    p * q < 2 * p + 2 * q := by sorry
