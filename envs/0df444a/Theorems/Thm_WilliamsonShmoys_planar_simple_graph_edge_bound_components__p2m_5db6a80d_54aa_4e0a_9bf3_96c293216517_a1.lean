-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_components__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_components__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:15:58.095992+00:00
-- url     : https://prove2.me/theorems/0735e628-0381-4bd6-9ee6-4833a51041e4
-- title:
--   Aggregate connected-subgraph bounds over components
-- statement:
--   If every nonempty connected induced subgraph has the planar edge bound for size at least three and the simple-graph bound for smaller sizes, then the whole graph has at most 3|V|−6 edges whenever |V|≥3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

namespace WilliamsonShmoys

end WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_components__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hLocal : ∀ (S : Finset V), S.Nonempty → let G : SimpleGraph {v // v ∈ S} := H.induce (fun v => v ∈ S); G.Connected → G.edgeSet.ncard ≤ if 3 ≤ Fintype.card {v // v ∈ S} then 3 * Fintype.card {v // v ∈ S} - 6 else Fintype.card {v // v ∈ S} - 1) (hcard : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
