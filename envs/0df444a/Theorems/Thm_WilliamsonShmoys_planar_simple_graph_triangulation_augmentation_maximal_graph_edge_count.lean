-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_triangulation_augmentation_maximal_graph_edge_count
-- name    : WilliamsonShmoys.planar_simple_graph_triangulation_augmentation_maximal_graph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:45:39.804927+00:00
-- url     : https://prove2.me/theorems/3396737a-f473-47a7-8a50-921e40ec9d74
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite ordered vertices with no strict drawable edge-set extension has exactly 3|V|−6 edges. The cardinality lower bound is essential: it excludes the small cases where the planar extremal formula does not apply. At exactly three vertices, maximality forces all three possible edges. For larger sizes, a proof route is to establish from maximality that the embedded graph is connected and every face is triangular, then apply Euler’s formula and count each face boundary edge twice. This isolates the topological and counting work from the parent theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_triangulation_augmentation_maximal_graph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
