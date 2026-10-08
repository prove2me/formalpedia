-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_isAtomic_of_mem_squareSideAtomicEdges
-- name    : ProofsInTheBook.Chapter20.isAtomic_of_mem_squareSideAtomicEdges
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:46:21.757677+00:00
-- url     : https://prove2.me/theorems/053ed4e8-6e69-471c-8d51-dedf4b9eb3f5
-- title:
--   A supported boundary-chain edge is a triangle atomic edge
-- statement:
--   Let D be a SquareDissection: a natural number n, a finite vertex type with decidable equality and injective real-plane coordinates, and n nondegenerate vertex triples whose closed convex hulls cover exactly $Q=[0,1]^2$, have pairwise disjoint topological interiors, and each have area $1/n$ (the rational quotient embedded in the reals). Area is half the absolute determinant. Triangle sides are subdivided at all vertices lying strictly between their endpoints, ordered by affine parameter. Consecutive vertices form unordered atomic edges; multiplicity counts occurrences across the triangle boundary lists. T-junctions and unused vertices are permitted. No oddness assumption on n is made here.
--
--   Let p,q,a,b be vertices with $p\ne q$. Assume $\{a,b\}$ is a consecutive atomic edge in the D-vertex subdivision of the segment from p to q, and that this whole p–q segment lies in the frontier of Q. Write $m=(\operatorname{coord}(a)+\operatorname{coord}(b))/2$. Assume additionally the following support condition: for every pair of D-vertices u,v whose coordinates lie in Q, if m belongs to the open segment between their coordinates, then both u and v lie on the closed p–q segment. Under these hypotheses, $\{a,b\}$ occurs in the atomic boundary list of at least one triangle of D. The quantified support condition is an explicit premise.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20E2Boundary.lean#L1319. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.” SquareDissection and atomic-edge definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L23.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

lemma ProofsInTheBook.Chapter20.isAtomic_of_mem_squareSideAtomicEdges
    {p q a b : D.vtx} (hpq : p ≠ q)
    (hside : s(a, b) ∈ sideAtomicEdges D p q)
    (hfront : segment ℝ (D.coord p) (D.coord q) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)))
    (support : ∀ u v : D.vtx,
      D.coord u ∈ unitSquareSetLocal → D.coord v ∈ unitSquareSetLocal →
      midpoint ℝ (D.coord a) (D.coord b) ∈
        openSegment ℝ (D.coord u) (D.coord v) →
      OnSide D p q u ∧ OnSide D p q v) :
    IsAtomicEdge D s(a, b) := by sorry
