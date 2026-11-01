-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_extension__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
-- name    : WilliamsonShmoys.planar_graph_has_maximal_planar_extension__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:45.472759+00:00
-- url     : https://prove2.me/theorems/0bdc9ebc-c764-435b-b9dd-f3dd83a4d5eb
-- title:
--   Extend a planar graph to a maximal planar supergraph
-- statement:
--   On a finite ordered vertex type, every graph with a planar drawing has a planar supergraph on the same vertices that has no strictly larger planar supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_maximal_planar_extension__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
