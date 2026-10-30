-- Prove2me | Theorems.Thm_WilliamsonShmoys_single_edge_drawable__p2m_17bd3fa2_c9c6_4c63_b04a_aaecb94be96d_a2
-- name    : WilliamsonShmoys.single_edge_drawable__p2m_17bd3fa2_c9c6_4c63_b04a_aaecb94be96d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:09.157044+00:00
-- url     : https://prove2.me/theorems/d648d857-6ced-4c57-84fe-55cb7040c70e
-- title:
--   A prescribed single edge has a planar drawing
-- statement:
--   For any two distinct vertices of `Fin 5`, there is a graph whose only edge joins those vertices and which has a drawing under the project's definition. The distinctness condition rules out loops.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.single_edge_drawable__p2m_17bd3fa2_c9c6_4c63_b04a_aaecb94be96d_a2 :
    ∀ i j : Fin 5, i ≠ j →
      ∃ L : SimpleGraph (Fin 5),
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ u v : Fin 5, L.Adj u v ↔
          (u = i ∧ v = j) ∨ (u = j ∧ v = i) := by sorry
