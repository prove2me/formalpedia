-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_edge_maximal_extension_e02108dc_5749_4b8c_85cc_e86e3f71cac7
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_edge_maximal_extension_e02108dc_5749_4b8c_85cc_e86e3f71cac7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:20:18.43433+00:00
-- url     : https://prove2.me/theorems/c4291689-ba07-4730-a08a-15219e905909
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_edge_maximal_extension_e02108dc_5749_4b8c_85cc_e86e3f71cac7
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by sorry
