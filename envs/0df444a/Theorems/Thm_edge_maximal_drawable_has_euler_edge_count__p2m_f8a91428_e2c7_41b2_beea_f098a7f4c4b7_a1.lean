-- Prove2me | Theorems.Thm_edge_maximal_drawable_has_euler_edge_count__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
-- name    : edge_maximal_drawable_has_euler_edge_count__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:55:46.054067+00:00
-- url     : https://prove2.me/theorems/ef27f67c-bfde-4fe0-af12-0939b2f8ce56
-- title:
--   Maximal drawable graphs have the Euler edge count
-- statement:
--   A drawable finite simple graph with at least three vertices that has no drawable proper edge supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem edge_maximal_drawable_has_euler_edge_count__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset ⊆ L.edgeFinset →
      L.edgeFinset ⊆ K.edgeFinset) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
