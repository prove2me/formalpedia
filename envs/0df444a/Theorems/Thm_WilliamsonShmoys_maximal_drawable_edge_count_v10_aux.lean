-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_v10_aux
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_v10_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:26:50.600713+00:00
-- url     : https://prove2.me/theorems/7c4723b3-86b9-49ee-93ab-a24e7ab5349e
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly 3|V|−6 edges. The proof route is to pass from the drawing to a planar embedding, establish the connectivity and face-boundary properties needed for maximality to force triangular faces, and use Euler’s formula and face-degree counting. The topological derivation remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_v10_aux {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 <= Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hmax : ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
