-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_map_one_edge_cut_faces_connected
-- name    : WilliamsonShmoys.triangular_map_one_edge_cut_faces_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T22:41:31.809855+00:00
-- url     : https://prove2.me/theorems/366bdaa9-a6a2-4c6d-b076-38aae69eb767
-- title:
--   Faces incident to a connected vertex set with one tree boundary edge are connected
-- statement:
--   In a triangular map, if a nonempty set of vertices is connected by tree edges and at most one tree edge crosses its boundary, then all faces with a corner in that set are connected using duals of edges outside the tree. This is the geometric core removed from the parent. A proof route follows the vertex rotations along the connected set and its boundary: each transition across a non-tree side supplies a cotree adjacency, while the possible single crossing tree edge only cuts the contour at one place and does not disconnect the incident faces. The assumptions cover the root case (no crossing edge) and the nonroot descendant-subtree case (one parent edge).
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
set_option autoImplicit false

theorem WilliamsonShmoys.triangular_map_one_edge_cut_faces_connected
    {V F : Type} [Fintype V] [Fintype F]
    {H : SimpleGraph V} (M : WilliamsonShmoys.TriangularMap H F)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree)
    (S : Set V) (hne : S.Nonempty) (hconn : (R.induce S).Connected)
    (hcut : ∀ a b c d : V, R.Adj a b → a ∈ S → b ∉ S →
      R.Adj c d → c ∈ S → d ∉ S →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    ((M.cotree R).induce
      {f : F | ∃ i : Fin 3, M.corner f i ∈ S}).Connected := by sorry
