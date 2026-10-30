-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_minimal_connected_supergraph__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
-- name    : WilliamsonShmoys.exists_minimal_connected_supergraph__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:02.938643+00:00
-- url     : https://prove2.me/theorems/403f53e7-e621-4069-88f6-7b776c045abd
-- title:
--   Finite graph has an inclusion-minimal connected extension
-- statement:
--   Every finite simple graph has a connected supergraph minimal under inclusion among connected supergraphs containing it. Choose an extension with the fewest edges; the empty vertex case has vacuous connectivity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.exists_minimal_connected_supergraph__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧
      ∀ K : SimpleGraph V, M ≤ K → K ≤ H → K.Connected → K = H := by sorry
