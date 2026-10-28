-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_finite_v2
-- name    : WilliamsonShmoys.planar_maximal_extension_finite_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:32:50.357395+00:00
-- url     : https://prove2.me/theorems/33a4a46e-57da-4cb3-a5be-90d0e33ac298
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type has a planar supergraph on that same type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_finite_v2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
