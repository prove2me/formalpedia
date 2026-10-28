-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangular_map
-- name    : WilliamsonShmoys.maximal_planar_graph_has_triangular_map
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:01:54.170006+00:00
-- url     : https://prove2.me/theorems/c83adf6f-1433-4aa5-8a45-3bb46fb3b994
-- title:
--   An inclusion maximal planar graph has a finite triangular map
-- statement:
--   A graph on at least three vertices that has a planar drawing and is inclusion maximal among planar-drawable graphs on the same vertex set admits a finite triangular map. This removes the topological embedding-to-map construction from the parent. A proof route is to extract the cyclic orders and faces from the drawing, use maximality to establish connectedness and that every face boundary is a triangle, then index the faces by a finite type and verify the dart bijection, distinct corners, vertex coverage, connectedness, and rotation transitivity. The lower bound on the vertex count is essential for the triangular-face conclusion and covers the smallest case, the three-vertex triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_has_triangular_map
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V), K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    ∃ (m : Nat), Nonempty (WilliamsonShmoys.TriangularMap K (Fin m)) := by
  sorry
