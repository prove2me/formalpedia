-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_edge_extension_count__p2m_3d35c422_26b2_44b6_842a_87c2ee457863_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_edge_extension_count__p2m_3d35c422_26b2_44b6_842a_87c2ee457863_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:20:57.774327+00:00
-- url     : https://prove2.me/theorems/2b94d345-c453-470c-8517-8648e22306c1
-- title:
--   Planar drawing extension reaches the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This is a planar augmentation lemma, stronger than the target’s conclusion because it does not assume maximality of the starting graph. Its proof must handle disconnected drawings and cut vertices as well as the face-triangulation and Euler-counting steps.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_edge_extension_count__p2m_3d35c422_26b2_44b6_842a_87c2ee457863_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, H ≤ L ∧ HasPlanarDrawingOn L ∧ 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
