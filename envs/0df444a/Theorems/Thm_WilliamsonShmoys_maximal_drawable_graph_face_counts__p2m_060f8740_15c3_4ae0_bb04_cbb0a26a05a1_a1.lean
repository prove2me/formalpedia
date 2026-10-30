-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_face_counts__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_face_counts__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:20.339733+00:00
-- url     : https://prove2.me/theorems/13694d57-9c40-45ab-89d1-4e7bf234d7f8
-- title:
--   Euler and triangular face counts for a maximal drawable graph
-- statement:
--   A finite crossing-free drawing that is maximal under drawable edge-set extensions and has at least three vertices admits a triangular-face count f satisfying Euler’s equation n + f = m + 2 and the face-edge incidence equation 3f = 2m, where m is the number of edges. The route is to obtain a sphere embedding from the drawing, use edge-maximality to rule out nontriangular faces and establish the needed connected embedding, then count each edge’s two face sides. The n ≥ 3 hypothesis covers the boundary case where the usual simple-graph facial argument applies; K3 gives f = 2. This is the remaining topological core, not an established result in the available local sources.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_face_counts__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 /\
      3 * f = 2 * H.edgeSet.ncard := by sorry
