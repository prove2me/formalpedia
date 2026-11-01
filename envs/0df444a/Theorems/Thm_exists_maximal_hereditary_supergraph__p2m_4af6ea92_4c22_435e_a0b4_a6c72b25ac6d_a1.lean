-- Prove2me | Theorems.Thm_exists_maximal_hereditary_supergraph__p2m_4af6ea92_4c22_435e_a0b4_a6c72b25ac6d_a1
-- name    : exists_maximal_hereditary_supergraph__p2m_4af6ea92_4c22_435e_a0b4_a6c72b25ac6d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:43.717202+00:00
-- url     : https://prove2.me/theorems/1d40241c-e17f-46de-aad3-cc1e6a1c7a6f
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   If a graph property on a finite vertex type is preserved when edges are removed, every graph satisfying it has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem exists_maximal_hereditary_supergraph__p2m_4af6ea92_4c22_435e_a0b4_a6c72b25ac6d_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hhered : ∀ {G H : SimpleGraph V},
      (∀ {u v : V}, H.Adj u v → G.Adj u v) → P G → P H)
    (M : SimpleGraph V) (hM : P M) :
    Exists fun N : SimpleGraph V =>
      (∀ {u v : V}, M.Adj u v → N.Adj u v) ∧
      P N ∧
      (∀ Q : SimpleGraph V,
        (∀ {u v : V}, N.Adj u v → Q.Adj u v) →
        P Q → Q = N) := by
  sorry
