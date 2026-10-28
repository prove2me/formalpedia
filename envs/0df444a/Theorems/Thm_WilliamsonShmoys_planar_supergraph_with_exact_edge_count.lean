-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_exact_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_with_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:30:24.648355+00:00
-- url     : https://prove2.me/theorems/f81ae0a6-df68-45c4-b5ad-262252871a49
-- title:
--   Planar supergraph extension with the maximal planar edge count
-- statement:
--   Every graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set with exactly 3n−6 edges. This is the planar triangulation extension step; for three vertices the extension is K₃, and disconnected components may first be joined by noncrossing edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_exact_edge_count {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ 3 * (Fintype.card V : Int) - 6 = (L.edgeSet.ncard : Int) := by sorry
