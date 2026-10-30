-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:33:52.457247+00:00
-- url     : https://prove2.me/theorems/0ce4b12f-9c91-441c-b797-1286dedfdf8a
-- title:
--   Adding an edge to a nonmaximal planar drawing
-- statement:
--   If a finite graph with at least three vertices has a planar drawing and fewer than 3|V|−6 edges, then some same-vertex-set strict edge supergraph also has a planar drawing. This is the augmentation step that lets the parent use maximality to rule out a strict edge-count deficit.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hCount : H.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊂ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
