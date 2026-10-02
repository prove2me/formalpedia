-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter12_chapter12
-- name    : ProofsInTheBook.Chapter12.chapter12
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:24:19.793652+00:00
-- url     : https://prove2.me/theorems/4b85f42a-582d-4091-a6f3-e5ca58a303ac
-- title:
--   The five possible degree pairs of a regular sphere map
-- statement:
--   Let D be a finite set of darts (with decidable equality in the formalization). A combinatorial map M consists of permutations $\alpha,\sigma$ of D, with $\alpha^2=1$ and $\alpha(d)\ne d$ for all darts. Put $\varphi=\sigma\circ\alpha$; the numbers V,E,F count the orbits of $\sigma,\alpha,\varphi$, respectively. Assume M is connected: any two darts can be joined by steps within one $\sigma$-orbit or across an $\alpha$-pair. Assume also $V-E+F=2$ (integer arithmetic). Let p,q be natural numbers, and assume every $\varphi$-orbit has exactly p darts and every $\sigma$-orbit has exactly q darts. If $p\ge3$, $q\ge3$, and $E>0$, then
--   $$(p,q)\in\{(3,3),(3,4),(4,3),(3,5),(5,3)\}.$$
--   This classifies the possible degree pairs under the stated combinatorial hypotheses; it does not assert existence or geometric uniqueness of solids.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter12.lean#L50. Topic reference: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 13, “Three applications of Euler’s formula”, pp. 89–94 (https://doi.org/10.1007/978-3-662-57265-8_13). The citation identifies the topic; the formal statement uses the specified combinatorial-map model.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter12
open ProofsInTheBook.Chapter12
open ProofsInTheBook.PlanarMap

theorem ProofsInTheBook.Chapter12.chapter12 {D : Type*} [Fintype D] [DecidableEq D] (M : CombMap D)
    (hsphere : M.IsSphereMap) {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hE : 0 < M.E)
    (hF : M.FaceRegular p) (hV : M.VertexRegular q) :
    (p = 3 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨ (p = 4 ∧ q = 3) ∨
      (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3) := by sorry
