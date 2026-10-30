-- Prove2me | Theorems.Thm_edgeSet_ncard_mono_of_le__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
-- name    : edgeSet_ncard_mono_of_le__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:33.434422+00:00
-- url     : https://prove2.me/theorems/7f55e582-48bf-4f72-ac47-1051b07e6aa8
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, inclusion of graphs implies that the edge-set cardinality is monotone.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem edgeSet_ncard_mono_of_le__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (h : LE.le G H) :
    LE.le G.edgeSet.ncard H.edgeSet.ncard := by
  sorry
