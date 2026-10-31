-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:44:17.431284+00:00
-- url     : https://prove2.me/theorems/4ded7af1-c0ed-47aa-b513-64b98071a5c3
-- title:
--   A drawable graph has a maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on that same type. Maximize over the finite family of supergraphs containing K that have a drawing. This removes the existence and maximality choice from the parent; a direct proof uses finiteness of the simple graphs on V. It holds without a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L := by sorry
