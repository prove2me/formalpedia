-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_14be45b2_4af8_4477_b67a_6d2fa4a08c68_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_14be45b2_4af8_4477_b67a_6d2fa4a08c68_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:12.687998+00:00
-- url     : https://prove2.me/theorems/60f46665-7c74-42d7-b1ac-33e75a012818
-- title:
--   Planar graphs admit a triangulating supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_14be45b2_4af8_4477_b67a_6d2fa4a08c68_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
