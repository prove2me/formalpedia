-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_f2db904c_5721_454a_bbac_7987a5a61819
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_f2db904c_5721_454a_bbac_7987a5a61819
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:48:53.933386+00:00
-- url     : https://prove2.me/theorems/3cb48610-7a77-41d9-a56e-df3f423e0d25
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A finite simple graph with a crossing-free drawing that is maximal among drawable supergraphs has exactly `3|V| - 6` edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_f2db904c_5721_454a_bbac_7987a5a61819
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hRmax : ∀ S : SimpleGraph V,
      R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R)
    (hCard : 3 ≤ Fintype.card V) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
