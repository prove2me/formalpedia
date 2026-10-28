-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximal_extension_f663d05c
-- name    : WilliamsonShmoys.planar_supergraph_edge_maximal_extension_f663d05c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:23:05.997897+00:00
-- url     : https://prove2.me/theorems/0d35725e-816f-424f-9345-5b76978a40c7
-- title:
--   Extend a planar graph to a maximal planar supergraph
-- statement:
--   Every planar graph on a finite ordered vertex type is contained in a planar supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_maximal_extension_f663d05c
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, L.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = L) := by sorry
