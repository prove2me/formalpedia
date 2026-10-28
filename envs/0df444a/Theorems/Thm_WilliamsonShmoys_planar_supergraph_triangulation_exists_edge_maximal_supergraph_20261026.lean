-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_exists_edge_maximal_supergraph_20261026
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_exists_edge_maximal_supergraph_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:24:55.813404+00:00
-- url     : https://prove2.me/theorems/b7d5e611-9f78-4b29-bcb8-9574c6bc66c3
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   This child removes the finite selection step from the parent. Its hypotheses include the exact drawing predicate and finite vertex type; the vertex-count lower bound is unnecessary for this step. The candidate supergraphs form a finite nonempty set, since there are finitely many simple graphs on V and K itself is drawable. Choose one with greatest edge-set cardinality. Any drawable supergraph containing it has at least as many edges, and strictly more if it differs, contradicting maximality. The statement is consistent for small vertex sets, including a single vertex, where K itself can be maximal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_triangulation_exists_edge_maximal_supergraph_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) := by sorry
