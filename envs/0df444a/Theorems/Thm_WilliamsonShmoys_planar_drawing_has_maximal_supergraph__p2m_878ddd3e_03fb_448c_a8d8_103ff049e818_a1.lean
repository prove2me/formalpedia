-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:31:05.492763+00:00
-- url     : https://prove2.me/theorems/21443123-0058-434c-a769-1fbcbbac1906
-- title:
--   Maximal drawable supergraph completion
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is inclusion maximal among drawable supergraphs and has at least as many edges as the original graph. Prove this by taking a maximal element of the finite collection of drawable supergraphs containing H; the edge-count inequality follows from edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) := by sorry
