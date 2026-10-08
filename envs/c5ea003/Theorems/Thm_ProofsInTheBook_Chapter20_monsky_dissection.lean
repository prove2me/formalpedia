-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_monsky_dissection
-- name    : ProofsInTheBook.Chapter20.monsky_dissection
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:17:44.361992+00:00
-- url     : https://prove2.me/theorems/64184e1c-8f5a-47bf-acab-cac73746a29a
-- title:
--   Monsky’s theorem for finite equal-area dissections of the unit square
-- statement:
--   There is no dissection of the unit square $[0,1]^2$ into an odd finite number n of equal-area nondegenerate triangles. Precisely, let V be a finite vertex type with decidable equality and an injective coordinate map $v:V\to\mathbb R^2$, and let $(a_i,b_i,c_i)\in V^3$ be specified for each $i\in\{0,\ldots,n-1\}$. Put $T_i=\operatorname{conv}\{v(a_i),v(b_i),v(c_i)\}$. Assume each oriented double area is nonzero, $\bigcup_iT_i=[0,1]^2$, the ordinary topological interiors of distinct $T_i$ are disjoint, and
--   $$\frac12\left|\det\big(v(b_i)-v(a_i),v(c_i)-v(a_i)\big)\right|=\frac1n$$
--   for every i, where the right-hand side is formally the rational quotient $1/n$ embedded into the reals. If n is odd, these data yield a contradiction.
--
--   The model permits a triangle corner to lie in the relative interior of another triangle's side. It assumes neither a face-to-face triangulation nor a supplied incidence or coloring certificate. The finite vertex type may also contain unused vertices; the structure does not require every vertex to occur as a triangle corner.
-- source:
--   Original headline: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionFinal.lean#L113. Exact geometric hypotheses: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L23. Area definition: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20.lean#L275. Repository topic: Proofs from THE BOOK, “One square and an odd number of triangles”; no edition numbering is asserted.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

theorem ProofsInTheBook.Chapter20.monsky_dissection (hn : Odd D.n) : False := by sorry
