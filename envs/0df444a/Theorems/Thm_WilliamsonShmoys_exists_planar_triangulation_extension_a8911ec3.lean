-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_a8911ec3
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension_a8911ec3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:41:14.294894+00:00
-- url     : https://prove2.me/theorems/c00979a8-2335-4ad2-bde4-30885009ac87
-- title:
--   Triangulation extension of a finite drawable graph
-- statement:
--   Every graph drawable under the supplied continuous-arc predicate on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The extension step triangulates the faces while retaining the vertices; Euler's formula supplies the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension_a8911ec3 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 <= Fintype.card V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) : ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
