-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_join_separated_vertices__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
-- name    : WilliamsonShmoys.planar_join_separated_vertices__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:35.047199+00:00
-- url     : https://prove2.me/theorems/0070a71d-6be0-4fa5-98df-35e57ae2fc30
-- title:
--   Join two disconnected vertices in a planar supergraph
-- statement:
--   For a finite ordered vertex type, if a graph has a crossing-free drawing and two vertices are in different connected components, there is a planar supergraph on the same vertices in which those vertices become connected. The extension may add other edges as needed. Non-reachability ensures the selected vertices are distinct. This isolates the geometric work of joining components while preserving a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_join_separated_vertices__p2m_f9b838b0_f6aa_487e_9e1a_71f80b7ae2c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    {u v : V} (hsep : ¬ H.Reachable u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Reachable u v ∧ HasPlanarDrawingOn K := by sorry
