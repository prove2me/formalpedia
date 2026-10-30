-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_induced_local__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_induced_local__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T06:16:05.902643+00:00
-- url     : https://prove2.me/theorems/5069c18c-1234-4231-99af-f0100e7ad2f3
-- title:
--   Local bounds for connected induced subgraphs of a drawn graph
-- statement:
--   For each nonempty vertex subset whose induced graph is connected, inherit the drawing and use the connected bound when the subset has at least three vertices; for subsets of size one or two, use simplicity to bound the edge count by |S|−1.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace WilliamsonShmoys

end WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_induced_local__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hcore : ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W), WilliamsonShmoys.HasPlanarDrawingOn G → G.Connected → 3 ≤ Fintype.card W → G.edgeSet.ncard ≤ 3 * Fintype.card W - 6) : ∀ (S : Finset V), S.Nonempty → let G : SimpleGraph {v // v ∈ S} := H.induce (fun v => v ∈ S); G.Connected → G.edgeSet.ncard ≤ if 3 ≤ Fintype.card {v // v ∈ S} then 3 * Fintype.card {v // v ∈ S} - 6 else Fintype.card {v // v ∈ S} - 1 := by sorry
