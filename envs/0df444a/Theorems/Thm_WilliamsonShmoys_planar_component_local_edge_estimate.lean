-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_local_edge_estimate
-- name    : WilliamsonShmoys.planar_component_local_edge_estimate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:25:38.179986+00:00
-- url     : https://prove2.me/theorems/6a637569-a6f2-448b-be8a-edb306a61b35
-- title:
--   Local edge estimates for planar components
-- statement:
--   For each nonempty connected component, bound its edge count by half its vertex count when it has fewer than three vertices, and by `3|S|−6` otherwise. The small cases follow from simplicity: a one-vertex graph has no edges and a two-vertex graph has at most one. For larger components, restrict the planar drawing and apply the connected planar edge bound from Euler’s formula, counting edge-face incidences and using the minimum face-boundary length. This child contains the main geometric proof obligation and makes the small-component boundary cases explicit.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_component_local_edge_estimate
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hConnected : ∀ S ∈ C, (H.induce (↑S : Set V)).Connected)
    (hDrawing : ∀ S ∈ C, WilliamsonShmoys.HasPlanarDrawingOn
      (H.induce (↑S : Set V))) :
    ∀ S ∈ C,
      (H.induce (↑S : Set V)).edgeSet.ncard ≤
        (if S.card < 3 then S.card / 2 else 3 * S.card - 6) := by sorry
