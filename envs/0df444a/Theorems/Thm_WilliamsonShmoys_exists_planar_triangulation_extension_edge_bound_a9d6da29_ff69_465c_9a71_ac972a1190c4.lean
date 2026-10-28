-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_edge_bound_a9d6da29_ff69_465c_9a71_ac972a1190c4
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension_edge_bound_a9d6da29_ff69_465c_9a71_ac972a1190c4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:26:41.742358+00:00
-- url     : https://prove2.me/theorems/818bf149-0bfd-4348-866a-626aa910ef08
-- title:
--   Triangulation extension for the planar edge lower bound
-- statement:
--   Every drawable finite simple graph on at least three vertices extends, on the same vertex type, to a drawable triangulation with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_triangulation_extension_edge_bound_a9d6da29_ff69_465c_9a71_ac972a1190c4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
