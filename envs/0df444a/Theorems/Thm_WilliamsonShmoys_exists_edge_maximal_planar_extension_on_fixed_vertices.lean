-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension_on_fixed_vertices
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension_on_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:03:29.185891+00:00
-- url     : https://prove2.me/theorems/8c9f26e1-9e58-4ea2-9511-cdf91e2c6f08
-- title:
--   A drawable graph has an edge-maximal drawable extension
-- statement:
--   On a finite fixed vertex set, any drawable simple graph is contained in a drawable supergraph that is maximal among drawable supergraphs on those same vertices. Choose a maximum-edge candidate from the finite set of simple graphs containing the input and having a drawing; any drawable supergraph with at least those edges must coincide with it. This applies to disconnected inputs as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension_on_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q →
        WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by sorry
