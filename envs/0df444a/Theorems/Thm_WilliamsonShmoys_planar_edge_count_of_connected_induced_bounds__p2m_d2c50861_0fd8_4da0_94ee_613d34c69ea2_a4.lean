-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_connected_induced_bounds__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
-- name    : WilliamsonShmoys.planar_edge_count_of_connected_induced_bounds__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:39.245466+00:00
-- url     : https://prove2.me/theorems/8c5d414d-1ded-412f-bc8e-a1e081bab435
-- title:
--   Combine connected induced-subgraph bounds across components
-- statement:
--   Combine the edge and vertex counts of the connected components. A component with at least three vertices uses hbound. A component of size one has no edges, and one of size two has at most one edge; each small component leaves at least three units of slack relative to three times its vertex count. If a large component exists it supplies six units of slack; otherwise, the total vertex count of at least three implies at least six units of slack across the small components. Prove this by partitioning the finite vertex type into connected components and summing the component inequalities. This isolates disconnected-graph bookkeeping from the topological child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_of_connected_induced_bounds__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hbound : ∀ (s : Set V) [Fintype {x // x ∈ s}],
      (G.induce s).Connected →
      3 ≤ Fintype.card {x // x ∈ s} →
      HasPlanarDrawingOn (G.induce s) →
      (letI : DecidableRel (G.induce s).Adj := Classical.decRel (G.induce s).Adj
       (G.induce s).edgeFinset.card + 6 ≤ 3 * Fintype.card {x // x ∈ s})) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
