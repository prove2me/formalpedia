-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_tight_edge_count_ea3c3bca_maximal_extension
-- name    : WilliamsonShmoys.planar_supergraph_tight_edge_count_ea3c3bca_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:35:53.864078+00:00
-- url     : https://prove2.me/theorems/359591bd-9f3d-4d89-acb4-1979b921d7eb
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a fixed finite vertex set of size at least three has a drawable supergraph that is maximal among drawable graphs on that same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_tight_edge_count_ea3c3bca_maximal_extension {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ (∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) := by sorry
