-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_planar_supergraph__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- name    : WilliamsonShmoys.planar_drawing_has_connected_planar_supergraph__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:51.486136+00:00
-- url     : https://prove2.me/theorems/2deb786e-0280-4a79-a944-d66b43964e65
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   Any finite simple graph with a drawing as defined in the target is a subgraph of a connected simple graph on the same vertices that also has such a drawing. The existing drawing definition is the source; the new geometric argument joins distinct components through the faces of the embedding without introducing crossings. This removes the disconnected-component bookkeeping from the parent. A proof must handle isolated vertices and two-vertex components as well as larger components. The remaining core obligation is to construct the added arcs while preserving the exact drawing predicates.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_connected_planar_supergraph__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      H.Connected ∧ HasPlanarDrawingOn H := by sorry
