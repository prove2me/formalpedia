-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
-- name    : WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:19.711384+00:00
-- url     : https://prove2.me/theorems/861504bb-9b69-4346-abcf-17510b6445ad
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strict drawable supergraph on the same vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     3 * Fintype.card V - 6 = H.edgeFinset.card) := by sorry
