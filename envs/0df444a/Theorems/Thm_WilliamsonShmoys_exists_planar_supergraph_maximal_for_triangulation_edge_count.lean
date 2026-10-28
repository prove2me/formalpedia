-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_for_triangulation_edge_count
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximal_for_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:31:34.584994+00:00
-- url     : https://prove2.me/theorems/c43ae2ba-7ce7-482d-a0fa-8e3a3878daf9
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   A graph with a planar drawing on the given finite vertex type has an inclusion-maximal planar supergraph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximal_for_triangulation_edge_count {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ H : SimpleGraph V, L ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = L := by sorry
