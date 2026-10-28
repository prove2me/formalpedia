-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_for_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_for_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:54:09.870645+00:00
-- url     : https://prove2.me/theorems/7995bf2e-7cfc-4100-a2e1-19e531640102
-- title:
--   Finite maximal drawable supergraph for edge count
-- statement:
--   Every drawable finite graph has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_for_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S) : ∃ T : SimpleGraph V, S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
