-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_of_nonempty__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a3
-- name    : WilliamsonShmoys.planar_drawing_add_bridge_of_nonempty__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:57:47.304839+00:00
-- url     : https://prove2.me/theorems/9ff46b9a-d59b-4c3c-9ec1-099be280d4ab
-- title:
--   Insert a bridge into a disconnected planar drawing on a nonempty vertex type
-- statement:
--   If a finite graph with at least two vertices has the given crossing-free drawing and is disconnected, it has a supergraph on the same vertices that retains such a drawing and adds an edge between vertices that were not previously connected. The cardinality condition excludes the empty type, where the required endpoint witnesses cannot exist.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_bridge_of_nonempty__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 2 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v, ¬ G.Reachable u v ∧ K.Adj u v := by sorry
