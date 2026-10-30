-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_has_drawable_strict_extension_dichotomy__p2m_5bb20037_ccd1_423f_b2f4_e98cccbfec38_a1
-- name    : WilliamsonShmoys.planar_sparse_graph_has_drawable_strict_extension_dichotomy__p2m_5bb20037_ccd1_423f_b2f4_e98cccbfec38_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:27:20.989984+00:00
-- url     : https://prove2.me/theorems/6aa45121-eedc-4241-b18d-7cc974f0060a
-- title:
--   Planar graphs admit an edge extension or are maximal planar
-- statement:
--   For a drawable finite simple graph with at least three vertices, either it has a strict drawable supergraph on the same vertex set or it has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_sparse_graph_has_drawable_strict_extension_dichotomy__p2m_5bb20037_ccd1_423f_b2f4_e98cccbfec38_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    (∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M) ∨
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
