-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_across_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1
-- name    : WilliamsonShmoys.planar_add_edge_across_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:03:52.35399+00:00
-- url     : https://prove2.me/theorems/779780b0-8268-4623-9635-e5c1e4db3c9e
-- title:
--   Insert an edge between specified disconnected vertices in a planar drawing
-- statement:
--   Given a planar drawing and two vertices in different components, there is a planar supergraph on the same vertices that adds the edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_across_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K) {u v : V} (hsep : ¬ K.Reachable u v) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.Adj u v ∧ ¬ K.Adj u v := by sorry
