-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_b9be61fe_8c1d_403c_9dc2_d4f84da24c92
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_b9be61fe_8c1d_403c_9dc2_d4f84da24c92
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:25:05.58598+00:00
-- url     : https://prove2.me/theorems/53dddbcd-67dc-454e-b4d2-26f3b045c421
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal graph satisfying the supplied crossing-free drawing predicate, with at least three vertices, has exactly 3n - 6 edges. A proof route is to derive connectedness and triangular faces from maximality, then use Euler’s formula and count each face boundary edge twice. This isolates the topological core needed by the parent. The statement includes the n ≥ 3 hypothesis, including the equality boundary n = 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_b9be61fe_8c1d_403c_9dc2_d4f84da24c92
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * (Fintype.card V : Int) - 6 = (M.edgeSet.ncard : Int) := by sorry
