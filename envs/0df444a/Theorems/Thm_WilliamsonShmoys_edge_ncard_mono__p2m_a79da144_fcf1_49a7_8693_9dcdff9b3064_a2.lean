-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_mono__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- name    : WilliamsonShmoys.edge_ncard_mono__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:52.34101+00:00
-- url     : https://prove2.me/theorems/5f7b3aad-6514-444c-b7cd-52d4f2e975b2
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, inclusion implies that the edge-set cardinality is monotone. Prove this by applying finite-set cardinality monotonicity to the edge-set inclusion induced by L ≤ H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_ncard_mono__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {L H : SimpleGraph V}
    (hLH : L ≤ H) :
    L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
