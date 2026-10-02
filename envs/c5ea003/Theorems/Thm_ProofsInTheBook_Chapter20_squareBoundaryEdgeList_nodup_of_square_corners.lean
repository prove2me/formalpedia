-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_squareBoundaryEdgeList_nodup_of_square_corners
-- name    : ProofsInTheBook.Chapter20.squareBoundaryEdgeList_nodup_of_square_corners
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:46:38.141623+00:00
-- url     : https://prove2.me/theorems/cfb0df9f-9b70-4f87-9932-82849576817a
-- title:
--   The square boundary chain has no repeated unordered edge
-- statement:
--   Let D be a SquareDissection: a natural number n, a finite vertex type with decidable equality and injective real-plane coordinates, and n nondegenerate vertex triples whose closed convex hulls cover exactly $Q=[0,1]^2$, have pairwise disjoint topological interiors, and each have area $1/n$ (the rational quotient embedded in the reals). Area is half the absolute determinant. Triangle sides are subdivided at all vertices lying strictly between their endpoints, ordered by affine parameter. Consecutive vertices form unordered atomic edges; multiplicity counts occurrences across the triangle boundary lists. T-junctions and unused vertices are permitted. No oddness assumption on n is made here.
--
--   Suppose vertices $c_{00},c_{10},c_{11},c_{01}$ have coordinates $(0,0),(1,0),(1,1),(0,1)$ respectively. Let L be the concatenation of the consecutive-edge lists along the four chains from $c_{00}$ to $c_{10}$ to $c_{11}$ to $c_{01}$ to $c_{00}$, each chain containing all D-vertices strictly between its endpoints in affine order.
--
--   The list L has no repeated unordered edge. This asserts no repetition of edges, not that the four chains have disjoint vertex sets.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20E2Boundary.lean#L1782. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.” SquareDissection and atomic-edge definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L23.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)
open scoped Classical

lemma ProofsInTheBook.Chapter20.squareBoundaryEdgeList_nodup_of_square_corners
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    (squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01).Nodup := by sorry
