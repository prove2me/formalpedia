-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_planar_extension_0319396f
-- name    : WilliamsonShmoys.triangulated_planar_extension_0319396f
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:22:35.629566+00:00
-- url     : https://prove2.me/theorems/af43d5e6-fb62-4820-8428-39fec5a766fc
-- title:
--   Extension to a drawable graph with the triangulation edge count
-- statement:
--   Any drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertex type with exactly 3|V|−6 edges. This captures the augmentation to a triangulated planar graph and its Euler-count consequence. The strict size boundary is retained; at three vertices, the extension can be the complete graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.triangulated_planar_extension_0319396f
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
