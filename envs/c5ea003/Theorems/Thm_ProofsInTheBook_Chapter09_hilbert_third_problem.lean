-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter09_hilbert_third_problem
-- name    : ProofsInTheBook.Chapter09.hilbert_third_problem
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T15:38:53.422456+00:00
-- url     : https://prove2.me/theorems/ac058859-8eaf-441c-9a1a-68718b4ef0a7
-- title:
--   The unit cube and coordinate regular tetrahedron have different Dehn invariants
-- statement:
--   Let $W=\mathbb R/(\mathbb Q\pi)$ as a rational vector space, and let $[\theta]\in W$ denote the class of a real angle $\theta$. For the encoded unit cube $C$ and the regular tetrahedron $T$ with vertices $(1,1,1)$, $(1,-1,-1)$, $(-1,1,-1)$ and $(-1,-1,1)$, define their rational Dehn sums by
--   $$D(P)=\sum_{e\in E(P)}\ell_e\otimes_{\mathbb Q}[\theta_e]\ \in\ \mathbb R\otimes_{\mathbb Q}W,$$
--   where $E(P)$ is the encoded finite edge set, $\ell_e$ its edge length, and $\theta_e$ its encoded interior dihedral angle. Then
--   $$D(C)\ne D(T).$$
--   The computed sums are $D(C)=0$ and $D(T)=(6\sqrt8)\otimes_{\mathbb Q}[\arccos(1/3)]\ne0$.
--
--   This is an explicit inequality of Dehn invariants. It does not assert equal volumes, a general dissection-invariance theorem, or geometric scissors noncongruence.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 10, “Hilbert’s third problem: decomposing polyhedra”, pp. 67–75 (https://doi.org/10.1007/978-3-662-57265-8_10). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter09.lean#L1464. The book citation identifies the topic; the selected declaration does not claim to reproduce the entire chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter09
open scoped BigOperators TensorProduct
open Polynomial Chebyshev
open ProofsInTheBook.Chapter09

theorem ProofsInTheBook.Chapter09.hilbert_third_problem :
    unitCubeDehnInvariantQ ≠ regularTetrahedronDehnInvariantQ := by sorry
