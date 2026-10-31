-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:04.80959+00:00
-- url     : https://prove2.me/theorems/ec87f3de-339b-432c-a6c1-ac3963609395
-- title:
--   Maximal drawable graphs attain the planar edge bound
-- statement:
--   If a drawable simple graph on at least three vertices admits no drawable strict supergraph on the same vertices, it has exactly `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) (hmax : ∀ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn Q → Q.edgeSet = N.edgeSet) : N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
