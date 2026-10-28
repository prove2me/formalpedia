-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_plane_map_edge_card
-- name    : WilliamsonShmoys.triangular_plane_map_edge_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:40:34.141489+00:00
-- url     : https://prove2.me/theorems/fd48fc89-c057-421d-82de-f06b6f74d537
-- title:
--   Count edges from triangular face data
-- statement:
--   From finite triangular face data with each graph edge on exactly two faces and Euler’s relation, count incidences in two ways and derive the edge-count formula. This counting step does not need additional hypotheses on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.triangular_plane_map_edge_card
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hFaces : ∃ (F : Type) (faceInst : Fintype F)
      (boundary : F → Finset (Sym2 V)),
      (∀ f, (boundary f).card = 3) ∧
      (∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet) ∧
      (∀ e ∈ L.edgeSet,
        ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2) ∧
      Fintype.card V + @Fintype.card F faceInst = L.edgeSet.ncard + 2) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
