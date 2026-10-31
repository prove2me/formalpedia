-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:30.534557+00:00
-- url     : https://prove2.me/theorems/785955c1-4844-4b43-8aa7-1c2f88e44dea
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V| − 6 edges. The route is to choose an inclusion-maximal drawable supergraph, show its faces are triangular, and apply Euler’s formula and face-edge incidence counting. This removes the topological extension and edge-counting work from the parent; formalizing those steps for the supplied continuous-arc predicate remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
