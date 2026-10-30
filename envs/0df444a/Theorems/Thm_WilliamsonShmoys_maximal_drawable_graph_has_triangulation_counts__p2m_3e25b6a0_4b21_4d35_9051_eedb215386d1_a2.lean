-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_counts__p2m_3e25b6a0_4b21_4d35_9051_eedb215386d1_a2
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulation_counts__p2m_3e25b6a0_4b21_4d35_9051_eedb215386d1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:47:33.332738+00:00
-- url     : https://prove2.me/theorems/f96fadc4-4ee6-4788-994d-723d6d164299
-- title:
--   Maximal drawable graphs admit triangular Euler counts
-- statement:
--   A drawable graph maximal under drawable edge additions on the same finite ordered vertex type, with at least three vertices, admits a face count f satisfying both the triangular edge-face incidence equation and Euler’s equation. The child removes the embedding, connectedness, and triangulation arguments from the parent; those arguments are its remaining core obligation. The n ≥ 3 hypothesis is needed for the maximal-planar triangulation result, and the proof must handle disconnected initial drawings rather than assuming connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulation_counts__p2m_3e25b6a0_4b21_4d35_9051_eedb215386d1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    ∃ f : Nat,
      2 * H.edgeSet.ncard = 3 * f ∧
      Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
