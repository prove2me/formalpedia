-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_has_drawable_strict_extension__p2m_19289cd0_8bc0_4354_9e78_5126f5795da0_a2
-- name    : WilliamsonShmoys.planar_sparse_graph_has_drawable_strict_extension__p2m_19289cd0_8bc0_4354_9e78_5126f5795da0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:11:07.547417+00:00
-- url     : https://prove2.me/theorems/5bb20037-ccd1-423f-b2f4-e98cccbfec38
-- title:
--   Sparse drawable graphs admit a strict drawable extension
-- statement:
--   Every drawable finite simple graph on at least three vertices with fewer than 3|V|−6 edges has a strict drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_sparse_graph_has_drawable_strict_extension__p2m_19289cd0_8bc0_4354_9e78_5126f5795da0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
