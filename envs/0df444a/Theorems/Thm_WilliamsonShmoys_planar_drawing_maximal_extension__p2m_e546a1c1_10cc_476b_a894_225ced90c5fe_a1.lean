-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:45:31.86526+00:00
-- url     : https://prove2.me/theorems/42a739af-e902-4f0f-92c2-b6d8532467cb
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   Every finite graph with a crossing-free drawing is contained, on the same vertex set, in an inclusion-maximal graph with a crossing-free drawing; the supergraph has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
