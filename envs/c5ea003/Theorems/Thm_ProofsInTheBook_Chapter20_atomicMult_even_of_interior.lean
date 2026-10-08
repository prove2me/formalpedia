-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_atomicMult_even_of_interior
-- name    : ProofsInTheBook.Chapter20.atomicMult_even_of_interior
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:46:12.110706+00:00
-- url     : https://prove2.me/theorems/c2ef191d-4481-49c9-beae-b64088426b55
-- title:
--   A nonboundary atomic edge has even multiplicity
-- statement:
--   Let D be a SquareDissection: a natural number n, a finite vertex type with decidable equality and injective real-plane coordinates, and n nondegenerate vertex triples whose closed convex hulls cover exactly $Q=[0,1]^2$, have pairwise disjoint topological interiors, and each have area $1/n$ (the rational quotient embedded in the reals). Area is half the absolute determinant. Triangle sides are subdivided at all vertices lying strictly between their endpoints, ordered by affine parameter. Consecutive vertices form unordered atomic edges; multiplicity counts occurrences across the triangle boundary lists. T-junctions and unused vertices are permitted. No oddness assumption on n is made here.
--
--   Let e be an unordered edge which occurs in a triangle atomic-edge list. Suppose its entire segment is not contained in the frontier of Q. Then its multiplicity across all triangle atomic boundary lists is even. The nonboundary premise is the negation of whole-segment containment; it does not require both endpoints to lie in the open square.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L2513. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.” The staged module contains a documented List.count proof compatibility port elsewhere in the file; this declaration is unchanged. Public and staged hashes and line positions are distinguished in source_evidence. SquareDissection and atomic-edge definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L23.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
open scoped Topology
variable (D : SquareDissection)

theorem ProofsInTheBook.Chapter20.atomicMult_even_of_interior (e : Sym2 D.vtx)
    (he : IsAtomicEdge D e) (hint : ¬ OnSquareBoundary D e) :
    Even (atomicMult D e) := by sorry
