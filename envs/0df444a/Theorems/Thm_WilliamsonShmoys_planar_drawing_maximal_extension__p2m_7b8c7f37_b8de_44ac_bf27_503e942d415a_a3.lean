-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:49:13.016843+00:00
-- url     : https://prove2.me/theorems/65670fb1-26f6-48e7-b847-d60e08421aa1
-- title:
--   Extend a finite planar drawing to an edge-maximal planar graph
-- statement:
--   A graph with a planar drawing has an edge-maximal planar supergraph on the same finite vertex type, with at least as many edges. Enumerating the finite set of supergraphs and maximizing edge count proves this extension step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
