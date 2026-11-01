-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_bounds_sum__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
-- name    : WilliamsonShmoys.planar_component_bounds_sum__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:56.24219+00:00
-- url     : https://prove2.me/theorems/9b39c159-5abf-402e-b341-b70b3524bea9
-- title:
--   Summing planar component edge bounds
-- statement:
--   For a disjoint finite partition covering the vertices, if the graph's edges are exactly accounted for by the induced graphs on the pieces and each piece has its appropriate planar edge bound, then the whole graph has at most `3|V|−6` edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem WilliamsonShmoys.planar_component_bounds_sum__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (C : V → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : Finset.univ.biUnion C = Finset.univ)
    (hedges : L.edgeSet.ncard = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard)
    (hlocal : ∀ i,
      if 3 ≤ (C i).card then
        (L.induce (fun v => v ∈ C i)).edgeSet.ncard ≤ 3 * (C i).card - 6
      else if 2 ≤ (C i).card then
        (L.induce (fun v => v ∈ C i)).edgeSet.ncard ≤ 1
      else
        (L.induce (fun v => v ∈ C i)).edgeSet.ncard = 0)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
