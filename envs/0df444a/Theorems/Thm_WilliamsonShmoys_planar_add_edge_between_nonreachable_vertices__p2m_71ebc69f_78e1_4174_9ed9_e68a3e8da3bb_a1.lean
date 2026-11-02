-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_nonreachable_vertices__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
-- name    : WilliamsonShmoys.planar_add_edge_between_nonreachable_vertices__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:08.817381+00:00
-- url     : https://prove2.me/theorems/61c492cb-f898-4cbe-b4f0-23e57d6c2689
-- title:
--   Joining distinct components preserves drawable planarity
-- statement:
--   If two vertices lie in different connected components of a finite drawable graph, the graph has a strict drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_edge_between_nonreachable_vertices__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (u v : V)
    (hsep : ¬ N.Reachable u v) (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P ≠ N ∧ HasPlanarDrawingOn P := by sorry
