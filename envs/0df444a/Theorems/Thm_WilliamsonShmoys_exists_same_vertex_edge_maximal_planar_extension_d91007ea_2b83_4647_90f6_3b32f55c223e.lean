-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_same_vertex_edge_maximal_planar_extension_d91007ea_2b83_4647_90f6_3b32f55c223e
-- name    : WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_extension_d91007ea_2b83_4647_90f6_3b32f55c223e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:13:01.311706+00:00
-- url     : https://prove2.me/theorems/181e3172-286b-428d-a71a-026d44a0adeb
-- title:
--   Finite planar graphs have an edge-maximal planar extension
-- statement:
--   A finite planar graph has a planar supergraph on the same vertex type that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_extension_d91007ea_2b83_4647_90f6_3b32f55c223e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, L.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ M : SimpleGraph V,
        (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        ∀ ⦃u v⦄, M.Adj u v → K.Adj u v) := by sorry
