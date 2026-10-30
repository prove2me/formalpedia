-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_connected__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:01.831507+00:00
-- url     : https://prove2.me/theorems/94246a03-8a78-4230-8fb4-c95831f5b666
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   This isolates the connectedness consequence needed before triangulating. A proof route is to use the given drawing of a disconnected graph to add a noncrossing edge between two components, contradicting maximality. The argument must account for the finite arc drawing and the at-least-three-vertices hypothesis; those hypotheses make this a specific topological step rather than an assumption that the graph is already connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_connected__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) : M.Connected := by sorry
