-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count_exists_maximal_drawable_extension
-- name    : WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_exists_maximal_drawable_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:46:18.627186+00:00
-- url     : https://prove2.me/theorems/6e79726b-4b90-42f0-bb91-eb82c7d4cd23
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is inclusion-maximal among drawable graphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_exists_maximal_drawable_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V, K ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
