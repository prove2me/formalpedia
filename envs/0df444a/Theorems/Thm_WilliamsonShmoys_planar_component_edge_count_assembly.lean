-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_edge_count_assembly
-- name    : WilliamsonShmoys.planar_component_edge_count_assembly
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:39:00.508285+00:00
-- url     : https://prove2.me/theorems/a4ece80d-5d6e-444e-873b-54c8dfc3ff5a
-- title:
--   Assemble planar component edge bounds
-- statement:
--   If each component of size at least three satisfies the planar edge bound, then the whole finite simple graph satisfies it when the total vertex count is at least three. Partition edges and vertices by component, use simplicity to bound components of size one or two, and sum the inequalities. This removes the disconnected-graph bookkeeping from the geometric child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_component_edge_count_assembly
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcomp : ∀ (c : M.ConnectedComponent),
      [Fintype {v : V // M.connectedComponentMk v = c}] →
      let S : Type := {v : V // M.connectedComponentMk v = c}
      let H : SimpleGraph S := M.induce (fun v => M.connectedComponentMk v = c)
      3 ≤ Fintype.card S → H.edgeSet.ncard ≤ 3 * Fintype.card S - 6) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
