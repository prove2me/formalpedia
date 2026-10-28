-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_for_edge_bound_6e31f1f9_6b57_4c6d_969e_fc2eb5bff20f
-- name    : WilliamsonShmoys.planar_triangulation_extension_for_edge_bound_6e31f1f9_6b57_4c6d_969e_fc2eb5bff20f
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:49:07.032604+00:00
-- url     : https://prove2.me/theorems/0f5abc15-12c9-4942-a13b-8bb8052f82b2
-- title:
--   Extend a finite planar graph to a triangulation with the edge bound
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices is a subgraph of a planar graph on the same vertices with exactly 3n−6 edges. The three-vertex boundary case is the triangle; the hypothesis excludes smaller vertex sets, where this count does not hold generally. The lemma removes the planar extension and Euler-counting work from the parent, which uses maximality to show the extension has exactly the same edges as the original graph. An independent proof route is to add drawable edges until no more can be added, establish that the resulting embedding has triangular faces, and apply Euler's formula together with face-edge incidence counting. This is the remaining core obligation; merely changing the lemma name does not reduce that mathematical work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_triangulation_extension_for_edge_bound_6e31f1f9_6b57_4c6d_969e_fc2eb5bff20f
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      (∀ {u v : V}, K.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
