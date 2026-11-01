-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_edgeSet_ncard_of_strict_extension__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
-- name    : WilliamsonShmoys.strict_edgeSet_ncard_of_strict_extension__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:11.576964+00:00
-- url     : https://prove2.me/theorems/e66a70cc-7ee9-4ebd-af65-1d2068e2feea
-- title:
--   Strict graph extension adds an edge
-- statement:
--   For graphs on a finite vertex type, a proper supergraph has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.strict_edgeSet_ncard_of_strict_extension__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hKH : ¬ K ≤ H) :
    H.edgeSet.ncard < K.edgeSet.ncard := by sorry
