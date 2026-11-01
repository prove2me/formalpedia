-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_2d4d5aa9_1174_4f98_adfa_d1e94ce87256_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_2d4d5aa9_1174_4f98_adfa_d1e94ce87256_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:22.294856+00:00
-- url     : https://prove2.me/theorems/742ffe8a-7b30-4bb8-be55-29e8d8d53fed
-- title:
--   Planar graph extension to a triangulation
-- statement:
--   Any finite simple graph with a planar drawing and at least three vertices is contained, on the same vertex set, in a planar graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_2d4d5aa9_1174_4f98_adfa_d1e94ce87256_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      P.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
