-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulated_extension_f4cab8f1_36b2_49a4_9100_a8a3956b9d6e
-- name    : WilliamsonShmoys.maximal_drawable_graph_triangulated_extension_f4cab8f1_36b2_49a4_9100_a8a3956b9d6e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:04:01.22229+00:00
-- url     : https://prove2.me/theorems/e02108dc-5749-4b8c-85cc-e86e3f71cac7
-- title:
--   Triangulated drawable extension with maximal planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This packages the triangulation extension and Euler-count argument; the parent uses it with maximality to identify the extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_triangulated_extension_f4cab8f1_36b2_49a4_9100_a8a3956b9d6e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
