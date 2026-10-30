-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_mono__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
-- name    : WilliamsonShmoys.edge_ncard_mono__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:29.455033+00:00
-- url     : https://prove2.me/theorems/75c760ff-048b-42aa-bb51-1d258b00a0ad
-- title:
--   Monotonicity of edge cardinality
-- statement:
--   Inclusion of edge sets implies monotonicity of their finite cardinalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_ncard_mono__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1 {V : Type} [Fintype V] [LinearOrder V] (L H : SimpleGraph V) (hEdges : L.edgeSet ⊆ H.edgeSet) : L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
