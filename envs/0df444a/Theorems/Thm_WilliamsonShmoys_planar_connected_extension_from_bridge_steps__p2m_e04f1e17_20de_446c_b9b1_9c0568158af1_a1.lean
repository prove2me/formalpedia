-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension_from_bridge_steps__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
-- name    : WilliamsonShmoys.planar_connected_extension_from_bridge_steps__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:49:09.316148+00:00
-- url     : https://prove2.me/theorems/8c10f930-cab6-4c60-91a8-1d9143f8c08c
-- title:
--   Finite maximal extension from drawable bridge steps
-- statement:
--   For a finite vertex type, if every disconnected drawable supergraph of a drawable graph admits a further drawable supergraph containing an edge between previously unreachable vertices, then there is a connected drawable supergraph whose edge count is at least the original's. This packages the finite graph maximization and edge-count reasoning independently of the topological bridge construction. A proof route is to choose an edge-maximal graph among the finite collection of drawable supergraphs; the bridge condition contradicts its maximality if it is disconnected. Graph inclusion then gives the edge-finset cardinality inequality. The nonempty hypothesis is preserved from the parent even though finite maximality itself does not require it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_extension_from_bridge_steps__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hne : 0 < Fintype.card V)
    (hbridge : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∃ u v : V, ¬ K.Reachable u v ∧ L.Adj u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj
         letI : DecidableRel H.Adj := Classical.decRel H.Adj
         G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
