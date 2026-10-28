-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_simpleGraph_property_extension__p2m_2d2efbeb_7ceb_4fa3_8371_f356ba71853f_a1
-- name    : WilliamsonShmoys.finite_maximal_simpleGraph_property_extension__p2m_2d2efbeb_7ceb_4fa3_8371_f356ba71853f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:41:19.551465+00:00
-- url     : https://prove2.me/theorems/dd4890eb-4344-46f7-9ca9-7e28390fe484
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   On a finite vertex type, if a graph T satisfies any property P, there is a graph R satisfying P that contains T and is maximal among graphs satisfying P that contain T.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_simpleGraph_property_extension__p2m_2d2efbeb_7ceb_4fa3_8371_f356ba71853f_a1
    {V : Type} [Fintype V]
    (T : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hT : P T) :
    ∃ R : SimpleGraph V,
      (∀ u v, T.Adj u v → R.Adj u v) ∧
      P R ∧
      (∀ S : SimpleGraph V,
        (∀ u v, T.Adj u v → S.Adj u v) →
        P S →
        (∀ u v, R.Adj u v → S.Adj u v) → S = R) := by sorry
