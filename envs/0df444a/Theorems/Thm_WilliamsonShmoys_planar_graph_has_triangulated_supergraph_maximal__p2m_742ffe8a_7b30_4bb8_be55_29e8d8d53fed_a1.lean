-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_maximal__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph_maximal__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:21.209919+00:00
-- url     : https://prove2.me/theorems/b8ded627-01f7-478f-9c89-d3e06a0d7e69
-- title:
--   Finite maximal planar extension
-- statement:
--   Any planar graph on a finite ordered vertex type is contained in a planar supergraph on the same vertices that has no strictly larger planar supergraph. This removes the finite maximization step from the parent; choose a planar supergraph with the maximum number of edges among the finitely many simple graphs on V. The boundary case |V|=3 is included and needs no special exclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph_maximal__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      (∀ Q : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn Q →
        (∀ u v, P.Adj u v → Q.Adj u v) →
        ∀ u v, Q.Adj u v → P.Adj u v) := by sorry
