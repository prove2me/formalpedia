-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:13:12.330823+00:00
-- url     : https://prove2.me/theorems/7b149b5a-6e79-4dbe-ac14-da128912b02b
-- title:
--   Existence of a maximal drawable supergraph on the same vertex set
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph on that same type that is maximal among drawable supergraphs under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) : ∃ S : SimpleGraph V, R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧ (∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T ≤ S) := by sorry
