-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_repair_0d3f2800_82dc_4ab9_ba1d_464ebc548881
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_repair_0d3f2800_82dc_4ab9_ba1d_464ebc548881
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:32:27.193429+00:00
-- url     : https://prove2.me/theorems/0beea86a-97f2-41ae-9007-21634e4df7c5
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that cannot be enlarged while preserving drawability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_repair_0d3f2800_82dc_4ab9_ba1d_464ebc548881 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
