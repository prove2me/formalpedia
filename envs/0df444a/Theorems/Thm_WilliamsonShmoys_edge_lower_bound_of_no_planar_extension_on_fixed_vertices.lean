-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_lower_bound_of_no_planar_extension_on_fixed_vertices
-- name    : WilliamsonShmoys.edge_lower_bound_of_no_planar_extension_on_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:07:08.622143+00:00
-- url     : https://prove2.me/theorems/fd5841b3-47d6-4110-a690-9c63bff57c51
-- title:
--   An edge-maximal drawable graph meets the planar edge lower bound
-- statement:
--   For at least three vertices, a drawable simple graph that has no strictly larger drawable supergraph on the same vertex set has at least 3|V|−6 edges. The independent proof route is to show maximality forces a connected triangulation, then apply Euler’s formula. The three-vertex boundary is included; without the lower-bound hypothesis, small maximal planar cases would need separate treatment.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_lower_bound_of_no_planar_extension_on_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V)
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
