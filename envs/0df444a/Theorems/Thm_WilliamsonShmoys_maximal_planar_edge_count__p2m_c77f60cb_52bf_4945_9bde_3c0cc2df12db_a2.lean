-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:39:31.160849+00:00
-- url     : https://prove2.me/theorems/cf998a55-167a-4517-9269-e98de5b379a5
-- title:
--   Edge count of an edge-maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices, maximal under drawable supergraph inclusion on the same vertex set, has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hKmax : ∀ L : SimpleGraph V, (∀ u v, K.Adj u v → L.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn L → (∀ u v, L.Adj u v → K.Adj u v)) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
