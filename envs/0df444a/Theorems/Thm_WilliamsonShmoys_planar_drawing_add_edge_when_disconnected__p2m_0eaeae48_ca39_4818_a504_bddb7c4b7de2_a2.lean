-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_when_disconnected__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
-- name    : WilliamsonShmoys.planar_drawing_add_edge_when_disconnected__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T07:02:18.665003+00:00
-- url     : https://prove2.me/theorems/238a233f-fe28-493b-899c-d8841aa16ff3
-- title:
--   Add a drawable edge to a disconnected drawing
-- statement:
--   This isolates the geometric insertion obligation left open by the attached definition: every finite disconnected graph with the specified drawing has a drawing-preserving supergraph with strictly more edges. It applies to disconnected graphs regardless of isolated vertices or the total vertex count; when a graph is already connected, the premise does not apply. A proof route is to replace the finitely many embedded edge arcs by polygonal arcs in disjoint neighborhoods, then use the component-face incidence structure to find two components bordering one face and connect them by an arc inside that face. This is the remaining topological core; the supplied source material did not provide a formal proof of it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_when_disconnected__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hDisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet ⊂ H.edgeSet := by sorry
