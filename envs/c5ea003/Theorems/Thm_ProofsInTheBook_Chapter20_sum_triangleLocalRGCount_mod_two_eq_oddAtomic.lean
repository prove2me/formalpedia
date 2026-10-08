-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_sum_triangleLocalRGCount_mod_two_eq_oddAtomic
-- name    : ProofsInTheBook.Chapter20.sum_triangleLocalRGCount_mod_two_eq_oddAtomic
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:46:38.237371+00:00
-- url     : https://prove2.me/theorems/941bfb58-6e07-4995-98bd-8bdc857538ca
-- title:
--   Triangle corner parity equals odd-multiplicity red–green edge parity
-- statement:
--   Let D be a SquareDissection: a natural number n, a finite vertex type with decidable equality and injective real-plane coordinates, and n nondegenerate vertex triples whose closed convex hulls cover exactly $Q=[0,1]^2$, have pairwise disjoint topological interiors, and each have area $1/n$ (the rational quotient embedded in the reals). Area is half the absolute determinant. Triangle sides are subdivided at all vertices lying strictly between their endpoints, ordered by affine parameter. Consecutive vertices form unordered atomic edges; multiplicity counts occurrences across the triangle boundary lists. T-junctions and unused vertices are permitted. No oddness assumption on n is made here.
--
--   Color each vertex by its coordinates using the chosen real 2-adic Monsky coloring. For triangle i let r_i be the number of red–green pairs among its three corner pairs. For an unordered vertex pair e let m(e) be its atomic multiplicity. Then
--   $$\sum_i r_i\equiv\#\{e:\ e\text{ has one red and one green endpoint and }m(e)\text{ is odd}\}\pmod2.$$
--   The set on the right ranges over all unordered pairs of D-vertices, including the diagonal convention; pairs of zero multiplicity do not contribute. This is a parity equality and does not itself assert oddness of either side.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionFinal.lean#L85. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.” SquareDissection and atomic-edge definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L23.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

theorem ProofsInTheBook.Chapter20.sum_triangleLocalRGCount_mod_two_eq_oddAtomic :
    (∑ i : Fin D.n, triangleLocalRGCount
        (realTwoAdicColor (D.coord (D.tri i).1),
         realTwoAdicColor (D.coord (D.tri i).2.1),
         realTwoAdicColor (D.coord (D.tri i).2.2))) % 2 =
      (Finset.univ.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
          Odd (atomicMult D e)).card % 2 := by sorry
