-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_edge_lower_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82
-- name    : WilliamsonShmoys.maximal_drawable_extension_edge_lower_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:16:21.558559+00:00
-- url     : https://prove2.me/theorems/97c34692-8381-40df-97e9-9134a912a845
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph that is maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension_edge_lower_bound_51bf81b4_48bc_4660_b9e1_3005ea79cb82
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
