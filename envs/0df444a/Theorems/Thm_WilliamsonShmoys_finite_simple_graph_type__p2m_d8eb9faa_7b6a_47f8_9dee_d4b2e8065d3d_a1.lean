-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simple_graph_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- name    : WilliamsonShmoys.finite_simple_graph_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:30.102204+00:00
-- url     : https://prove2.me/theorems/fb35f7f6-199c-4def-949d-9b141aad2903
-- title:
--   Finiteness of graphs on a finite vertex type
-- statement:
--   There are only finitely many simple graphs on a finite vertex type. This gives the parent proof a finite carrier over which to choose a maximal drawable extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simple_graph_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
    {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
