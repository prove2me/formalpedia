-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_extension_edge_bound
-- name    : WilliamsonShmoys.planar_drawable_extension_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:38:39.988087+00:00
-- url     : https://prove2.me/theorems/a2aea985-ee54-4b1c-b2ba-71370f50e997
-- title:
--   Drawable extension edge lower bound
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on that same vertex type with at least 3|V|−6 edges. This removes the planar augmentation and Euler-count work from the parent. A proof route is to extend the finite drawing by drawable edges until it is maximal on the fixed vertex set, then use planar triangulation and Euler counting. The disconnected case and the boundary case |V| = 3 must be covered; the extension must preserve the given drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_extension_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
