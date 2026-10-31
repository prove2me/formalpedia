-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph__p2m_dedf5137_e1df_470f_a755_e725cf271f52_a2
-- name    : WilliamsonShmoys.exists_edge_maximal_drawable_supergraph__p2m_dedf5137_e1df_470f_a755_e725cf271f52_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:12:58.104272+00:00
-- url     : https://prove2.me/theorems/8f785194-4ebf-4934-9ef0-448f353be8a7
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite fixed vertex type is contained in a drawable supergraph with no strictly larger drawable supergraph on that type. This removes the existence and maximality choice from the parent. Independently, one can maximize edge count among the finite set of drawable supergraphs containing G; the initial graph G ensures that set is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_edge_maximal_drawable_supergraph__p2m_dedf5137_e1df_470f_a755_e725cf271f52_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
