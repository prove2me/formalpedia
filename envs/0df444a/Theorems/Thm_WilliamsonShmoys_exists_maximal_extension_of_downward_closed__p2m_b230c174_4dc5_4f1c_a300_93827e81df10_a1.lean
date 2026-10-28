-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_downward_closed__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_of_downward_closed__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:41:38.214201+00:00
-- url     : https://prove2.me/theorems/59fa87a3-70b8-4c3b-978b-2ea5ba62a9ba
-- title:
--   Maximal extension for a finite downward-closed graph property
-- statement:
--   For a finite vertex type, any graph satisfying a downward-closed property has a supergraph satisfying that property that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_of_downward_closed__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (L : SimpleGraph V) (hL : P L) :
    ∃ K : SimpleGraph V, L ≤ K ∧ P K ∧
      ∀ H : SimpleGraph V, K ≤ H → P H → H = K := by sorry
