-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:21:51.668106+00:00
-- url     : https://prove2.me/theorems/b970fbf3-bcfc-4d92-8b88-46bd045bfd9d
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable graph on at least three finite ordered vertices that has no strictly larger drawable supergraph on the same vertex set has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
