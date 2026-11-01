-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
-- name    : WilliamsonShmoys.planar_edge_maximal_extension__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:00:52.823298+00:00
-- url     : https://prove2.me/theorems/a3381679-1a4a-4690-bb58-30d1058a3987
-- title:
--   Extension to an edge-maximal planar graph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type is contained in a drawable graph that is maximal among drawable graphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_maximal_extension__p2m_e52a5279_3bb4_4190_b470_b345cecfed03_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      (HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
          (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
          (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v)) := by sorry
