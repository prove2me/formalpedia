-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_triangulation_extension_87a22553
-- name    : WilliamsonShmoys.maximal_drawable_triangulation_extension_87a22553
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:09:31.575997+00:00
-- url     : https://prove2.me/theorems/d974173a-f270-49ae-9bfa-572de673fb28
-- title:
--   Triangulation extension of a drawable graph on a fixed vertex set
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This is the fixed-vertex triangulation extension fact; the extension need not be maximal in the statement because its edge count and the parent’s maximality identify it with H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_triangulation_extension_87a22553 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
