-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:14.691813+00:00
-- url     : https://prove2.me/theorems/582f02ed-53a8-4c98-b373-42920d89e7d2
-- title:
--   Monotonicity of finite edge-set cardinality
-- statement:
--   For finite simple graphs on the same vertex type, graph inclusion implies that the cardinality of the first edge set is at most the cardinality of the second. Prove this by showing the first edge set is included in the second and applying finite set-cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
    {V : Type} [Fintype V]
    (H K : SimpleGraph V) (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
