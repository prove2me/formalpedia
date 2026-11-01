-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_bound__p2m_c6470163_a9cd_431f_b992_62a6706eed9c_a1
-- name    : WilliamsonShmoys.planar_drawing_completion_edge_bound__p2m_c6470163_a9cd_431f_b992_62a6706eed9c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:43.421976+00:00
-- url     : https://prove2.me/theorems/8a1de5a7-e6e0-49bf-bc1c-04323822a27c
-- title:
--   Drawable graphs extend to the planar edge bound
-- statement:
--   Every finite graph with a crossing-free drawing on at least three vertices is a subgraph of another graph with such a drawing and at least 3|V|−6 edges. The parent applies inclusion maximality to identify this supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion_edge_bound__p2m_c6470163_a9cd_431f_b992_62a6706eed9c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ u v, L.Adj u v → M.Adj u v) ∧
      3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
