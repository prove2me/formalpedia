-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_cut_bridge__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
-- name    : WilliamsonShmoys.planar_drawing_add_cut_bridge__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:44.408606+00:00
-- url     : https://prove2.me/theorems/eb8f4cd8-f0b2-4542-934a-57c382c5e901
-- title:
--   Add a bridge across an edge-free cut in a planar drawing
-- statement:
--   If a planar graph has no edge crossing a vertex cut, any chosen vertex on one side can be joined by a new edge to any chosen vertex on the other side while retaining a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_cut_bridge__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    {u v : V} (s : Set V)
    (hu : u ∈ s) (hv : v ∉ s)
    (hcut : ∀ x y, G.Adj x y → (x ∈ s ↔ y ∈ s)) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by sorry
