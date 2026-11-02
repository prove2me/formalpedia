-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_good_supergraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
-- name    : WilliamsonShmoys.exists_maximal_good_supergraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:55:41.646998+00:00
-- url     : https://prove2.me/theorems/87f6b0d9-fd5c-46d9-b554-b7f0d246fc29
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   On a finite vertex type, every graph satisfying a property closed under subgraphs is contained in a supergraph maximal among graphs with that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_good_supergraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
    {V : Type} [Fintype V]
    (P : SimpleGraph V) (Good : SimpleGraph V → Prop)
    (hP : Good P)
    (hsub : ∀ {G H : SimpleGraph V}, H ≤ G → Good G → Good H) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Good Q ∧
      ∀ R : SimpleGraph V, Q ≤ R → Good R → R ≤ Q := by sorry
