-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_extension_exists_maximal_supergraph
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_extension_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:35:59.13703+00:00
-- url     : https://prove2.me/theorems/ef6358eb-f2ce-4c5d-ae59-a4a7c6c5624b
-- title:
--   A finite planar graph has a maximal planar supergraph
-- statement:
--   Every finite graph with the supplied planar drawing is contained in a planar supergraph on the same vertex type that has no strict planar supergraph on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_extension_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V => K <= L /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      ∀ M : SimpleGraph V, L <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M <= L := by sorry
