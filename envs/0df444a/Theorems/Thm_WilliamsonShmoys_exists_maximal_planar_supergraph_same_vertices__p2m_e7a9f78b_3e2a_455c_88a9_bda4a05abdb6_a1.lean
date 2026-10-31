-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:21.427916+00:00
-- url     : https://prove2.me/theorems/2df6cf7e-c4ff-4f1c-945c-2e656bad6781
-- title:
--   A drawable graph has a maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable finite graph has an inclusion-maximal drawable supergraph on the same vertex type. The finite family of simple graphs on the fixed vertex type gives a direct proof route by maximizing over drawable supergraphs containing K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L := by sorry
