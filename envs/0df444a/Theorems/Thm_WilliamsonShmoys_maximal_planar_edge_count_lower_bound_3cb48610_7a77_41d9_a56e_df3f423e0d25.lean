-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:14:34.50711+00:00
-- url     : https://prove2.me/theorems/1f319a38-ec2f-4e98-b914-4c5152eec225
-- title:
--   Lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least three times its number of vertices minus six edges. Prove this by extending the drawing to a triangulation without adding vertices, applying maximality to the extension, and counting the triangulation’s edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hRmax : ∀ S : SimpleGraph V,
      R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ R.edgeSet.ncard + 6 := by sorry
