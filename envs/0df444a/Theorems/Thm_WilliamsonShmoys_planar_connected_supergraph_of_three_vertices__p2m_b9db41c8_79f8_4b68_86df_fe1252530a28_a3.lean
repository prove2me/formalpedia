-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_of_three_vertices__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a3
-- name    : WilliamsonShmoys.planar_connected_supergraph_of_three_vertices__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:57:23.280584+00:00
-- url     : https://prove2.me/theorems/b288f1f9-9e57-4851-a40a-3efdbb7536d5
-- title:
--   Connected planar supergraph when there are at least three vertices
-- statement:
--   A finite graph with a crossing-free drawing and at least three vertices has a connected simple supergraph on the same vertices that also has a crossing-free drawing. The size hypothesis excludes the empty-type counterexample to the earlier child statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph_of_three_vertices__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
