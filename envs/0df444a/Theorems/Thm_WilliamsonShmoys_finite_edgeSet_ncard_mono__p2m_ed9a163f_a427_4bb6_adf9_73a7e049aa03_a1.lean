-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_edgeSet_ncard_mono__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
-- name    : WilliamsonShmoys_finite_edgeSet_ncard_mono__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:25:21.035988+00:00
-- url     : https://prove2.me/theorems/20f9c358-ef7e-43ba-bde9-7cedc7f99252
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   For finite vertex types, inclusion of simple graphs implies that the smaller graph’s edge set has no greater cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_finite_edgeSet_ncard_mono__p2m_ed9a163f_a427_4bb6_adf9_73a7e049aa03_a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
