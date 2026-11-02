-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_bound__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:12:28.710474+00:00
-- url     : https://prove2.me/theorems/c58532ae-f567-4d99-af18-913e5bd1d27d
-- title:
--   Maximal drawable extension on the same vertex set
-- statement:
--   Every drawable finite graph has an edge-maximal drawable supergraph on the same vertex set, with at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
       letI : DecidableRel M.Adj := Classical.decRel M.Adj;
       G.edgeFinset.card ≤ M.edgeFinset.card) ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
