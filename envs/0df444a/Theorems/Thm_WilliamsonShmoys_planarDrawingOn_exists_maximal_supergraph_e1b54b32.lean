-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_supergraph_e1b54b32
-- name    : WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_e1b54b32
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:23:32.611121+00:00
-- url     : https://prove2.me/theorems/449d5973-713a-47a0-8a6f-2a9b0a265a6c
-- title:
--   A planar graph has an edge-maximal planar supergraph
-- statement:
--   Every finite planar graph on at least three vertices is contained in a planar graph on the same vertex type with no strictly larger planar supergraph. The proof chooses a graph with maximum edge-set cardinality among the finite family of planar supergraphs containing the input.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_e1b54b32
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V,
        N.edgeSet ⊂ P.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
