-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_8e6fe4ee_76fd_4caa_8f38_7058c432af92
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_8e6fe4ee_76fd_4caa_8f38_7058c432af92
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:32:47.690078+00:00
-- url     : https://prove2.me/theorems/1e87e3e3-516a-437b-949a-8f1cf81adf5f
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   For a drawable graph on a finite ordered vertex type, there is a drawable supergraph maximal under inclusion among drawable supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_8e6fe4ee_76fd_4caa_8f38_7058c432af92 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) := by sorry
