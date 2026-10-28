-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:31:50.755041+00:00
-- url     : https://prove2.me/theorems/86477505-ee2f-4ad5-9760-02e87e5d0f7f
-- title:
--   Existence of a maximal drawable supergraph on the fixed vertex type
-- statement:
--   Every graph with the specified planar drawing extends, on the same finite vertex type, to a drawable supergraph maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
