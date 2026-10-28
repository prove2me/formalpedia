-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:31:44.392825+00:00
-- url     : https://prove2.me/theorems/18c10299-fe32-4c5c-9c93-e9dc19d5488d
-- title:
--   Maximal planar supergraph extension
-- statement:
--   Every graph with the specified planar drawing has a same-vertex-type planar supergraph maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
