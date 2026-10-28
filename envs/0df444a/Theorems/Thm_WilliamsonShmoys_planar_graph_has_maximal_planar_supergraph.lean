-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_supergraph
-- name    : WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:27:21.978323+00:00
-- url     : https://prove2.me/theorems/4b7f1622-a320-4002-997c-54576a8971da
-- title:
--   Extend a planar graph to a maximal planar supergraph
-- statement:
--   Every graph with a planar drawing on a finite vertex type is contained in a graph with a planar drawing that is maximal among supergraphs on that same vertex type. This removes the need for the parent proof to construct a maximal extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ Q : SimpleGraph V,
      N ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        ∀ R : SimpleGraph V,
          Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by sorry
