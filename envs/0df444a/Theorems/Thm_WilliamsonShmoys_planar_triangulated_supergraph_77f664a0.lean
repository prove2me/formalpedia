-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_supergraph_77f664a0
-- name    : WilliamsonShmoys.planar_triangulated_supergraph_77f664a0
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:18:57.738478+00:00
-- url     : https://prove2.me/theorems/03ffcefc-9f75-4be2-a57c-3e6bbb666115
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   A drawable graph on at least three vertices is contained, on the same vertex set, in a drawable graph with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulated_supergraph_77f664a0
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      (∀ u v, H.Adj u v → G.Adj u v) ∧
      HasPlanarDrawingOn G ∧
      G.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
