-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ac4b6b7c_6a36_45ce_9f61_962873444f22_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ac4b6b7c_6a36_45ce_9f61_962873444f22_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:35.747193+00:00
-- url     : https://prove2.me/theorems/0e6993dc-8a82-45ba-97f3-22ae93ae0c24
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar graph on at least three vertices that admits no strictly larger planar supergraph on the same vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ac4b6b7c_6a36_45ce_9f61_962873444f22_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) (hmax : ∀ K : SimpleGraph V, (∀ u v, H.Adj u v → K.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn K → (∀ u v, K.Adj u v → H.Adj u v)) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
