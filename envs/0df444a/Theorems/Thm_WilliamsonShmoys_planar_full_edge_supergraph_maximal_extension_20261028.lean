-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_full_edge_supergraph_maximal_extension_20261028
-- name    : WilliamsonShmoys.planar_full_edge_supergraph_maximal_extension_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:20:46.976792+00:00
-- url     : https://prove2.me/theorems/23729374-d99b-483b-bf5f-e3a0a06161fb
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Any simply drawn planar graph on a finite ordered vertex type is contained in a planar supergraph on the same vertices that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_full_edge_supergraph_maximal_extension_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by sorry
