-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_2d07592e_de05_4bbe_bc2f_be57428238dd_a3
-- name    : WilliamsonShmoys_planar_triangulation_extension__p2m_2d07592e_de05_4bbe_bc2f_be57428238dd_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:08:08.1661+00:00
-- url     : https://prove2.me/theorems/f718c55c-a2b6-42f7-bccf-89c606c1e3eb
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   Every graph with a drawing satisfying the supplied crossing-free arc definition, on a finite linearly ordered vertex type with at least three vertices, is a subgraph of a planar graph on the same vertex type with exactly 3|V|−6 edges. The parent applies maximality to identify that extension with the original graph, then obtains the lower bound by arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_planar_triangulation_extension__p2m_2d07592e_de05_4bbe_bc2f_be57428238dd_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj
         L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
