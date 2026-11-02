-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
-- name    : WilliamsonShmoys.planar_edge_maximal_extension__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:36:39.462212+00:00
-- url     : https://prove2.me/theorems/e472cbd3-427a-4623-8f32-b9aff130ed8d
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_maximal_extension__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hQ : HasPlanarDrawingOn Q) (hcard : 3 ≤ Fintype.card V) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R := by sorry
