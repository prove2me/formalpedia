-- Prove2me | Theorems.Thm_planarDrawingOn_maximal_supergraph_edge_bound
-- name    : planarDrawingOn_maximal_supergraph_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:38:11.362445+00:00
-- url     : https://prove2.me/theorems/0f32b84e-1909-420f-8d03-c02b7d464669
-- title:
--   Edge bound for an inclusion-maximal planar drawing
-- statement:
--   A planar graph on at least three vertices that admits no strictly larger planar supergraph on those same vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem planarDrawingOn_maximal_supergraph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, L ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by sorry
