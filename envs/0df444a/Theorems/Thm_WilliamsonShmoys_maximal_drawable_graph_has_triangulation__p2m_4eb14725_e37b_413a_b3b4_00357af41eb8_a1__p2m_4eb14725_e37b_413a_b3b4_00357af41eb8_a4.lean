-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a4
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:04.788995+00:00
-- url     : https://prove2.me/theorems/637d8540-4fa2-4bdf-8eaf-997caf9c33c1
-- title:
--   Drawable supergraph attaining the planar edge bound
-- statement:
--   Every drawable simple graph on the same finite linearly ordered vertex type with at least three vertices has a drawable supergraph whose edge count is 3|V|−6, with the count stated for any decidable adjacency instance.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a4 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) [DecidableRel N.Adj] (hcard : 3 ≤ Fintype.card V) (hN : HasPlanarDrawingOn N) : ∃ (P : SimpleGraph V), N ≤ P ∧ HasPlanarDrawingOn P ∧ (∀ [DecidableRel P.Adj], P.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
