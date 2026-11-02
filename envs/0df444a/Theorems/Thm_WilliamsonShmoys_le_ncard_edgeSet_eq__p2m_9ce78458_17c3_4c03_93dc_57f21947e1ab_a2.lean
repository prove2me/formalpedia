-- Prove2me | Theorems.Thm_WilliamsonShmoys_le_ncard_edgeSet_eq__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
-- name    : WilliamsonShmoys.le_ncard_edgeSet_eq__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:25:57.49939+00:00
-- url     : https://prove2.me/theorems/fba75840-7620-41fb-b437-a1c510c95c5f
-- title:
--   Edge-set maximality implies graph equality
-- statement:
--   For simple graphs on a finite vertex type, subgraph inclusion together with at least as many edges forces equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.le_ncard_edgeSet_eq__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
    {V : Type} [Fintype V] [DecidableEq V]
    {H K : SimpleGraph V} (hHK : H ≤ K)
    (hcard : Set.ncard H.edgeSet ≥ Set.ncard K.edgeSet) : K = H := by sorry
