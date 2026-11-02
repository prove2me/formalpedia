-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraph_maximal__p2m_e472cbd3_427a_4623_8f32_b9aff130ed8d_a2
-- name    : WilliamsonShmoys.finite_drawable_supergraph_maximal__p2m_e472cbd3_427a_4623_8f32_b9aff130ed8d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:53:41.963658+00:00
-- url     : https://prove2.me/theorems/6b4462b4-5135-411a-8c3b-882d1de9cea4
-- title:
--   Maximal drawable supergraph on a finite vertex type
-- statement:
--   For a finite linearly ordered vertex type, every graph with a planar drawing has a drawable supergraph that is maximal among drawable graphs on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.finite_drawable_supergraph_maximal__p2m_e472cbd3_427a_4623_8f32_b9aff130ed8d_a2 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hQ : HasPlanarDrawingOn Q) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R := by sorry
