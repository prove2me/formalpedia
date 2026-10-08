-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_atomicBoundary_mem_squareBoundaryEdgeList_of_square_corners
-- name    : ProofsInTheBook.Chapter20.atomicBoundary_mem_squareBoundaryEdgeList_of_square_corners
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:46:02.257932+00:00
-- url     : https://prove2.me/theorems/3a10f6b4-201c-4436-b68d-593bb60d8832
-- title:
--   Every boundary atomic edge occurs in the square boundary chain
-- statement:
--   Let D be a SquareDissection: a natural number n, a finite vertex type with decidable equality and injective real-plane coordinates, and n nondegenerate vertex triples whose closed convex hulls cover exactly $Q=[0,1]^2$, have pairwise disjoint topological interiors, and each have area $1/n$ (the rational quotient embedded in the reals). Area is half the absolute determinant. Triangle sides are subdivided at all vertices lying strictly between their endpoints, ordered by affine parameter. Consecutive vertices form unordered atomic edges; multiplicity counts occurrences across the triangle boundary lists. T-junctions and unused vertices are permitted. No oddness assumption on n is made here.
--
--   Suppose vertices $c_{00},c_{10},c_{11},c_{01}$ have coordinates $(0,0),(1,0),(1,1),(0,1)$ respectively. Let L be the concatenation of the consecutive-edge lists along the four chains from $c_{00}$ to $c_{10}$ to $c_{11}$ to $c_{01}$ to $c_{00}$, each chain containing all D-vertices strictly between its endpoints in affine order.
--
--   If an unordered edge e occurs in some triangle atomic-edge list and its entire geometric segment lies in the frontier of Q, then e belongs to the finite set of entries of L. This is the inclusion from boundary atomic edges to the boundary chain.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20E2Boundary.lean#L1876. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.” SquareDissection and atomic-edge definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L23.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

lemma ProofsInTheBook.Chapter20.atomicBoundary_mem_squareBoundaryEdgeList_of_square_corners
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    {e : Sym2 D.vtx}
    (he : IsAtomicEdge D e ∧ OnSquareBoundary D e) :
    e ∈ (squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01).toFinset := by sorry
