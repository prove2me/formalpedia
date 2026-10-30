-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_graph_extension_edge_ncard__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1
-- name    : WilliamsonShmoys.strict_graph_extension_edge_ncard__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:13.734106+00:00
-- url     : https://prove2.me/theorems/ee430e38-0f79-41d6-a480-13bc34d7232a
-- title:
--   Strict graph extensions have more edges
-- statement:
--   A proper subgraph of a graph on a finite vertex type has strictly fewer edges. This removes the cardinality argument from the parent: apply strict ncard monotonicity to the finite edge sets under the proper inclusion. The strictness hypothesis is essential and is used only when the proposed extension differs from K. The remaining core obligation is to establish finiteness of both edge sets and apply the finite-set ncard theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.strict_graph_extension_edge_ncard__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1 {V : Type} [Fintype V] [DecidableEq V] {G L : SimpleGraph V} (h : G < L) : G.edgeSet.ncard < L.edgeSet.ncard := by sorry
