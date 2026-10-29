-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_superset_of_hereditary__p2m_ff3915fc_abca_4176_9ba9_489c8aaa0e6f_a1
-- name    : WilliamsonShmoys.exists_maximal_superset_of_hereditary__p2m_ff3915fc_abca_4176_9ba9_489c8aaa0e6f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:18:33.395139+00:00
-- url     : https://prove2.me/theorems/7486eb50-a720-420d-b854-621569123c00
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   For a finite vertex type, any edge-hereditary property possessed by a graph has a supergraph with that property to which no missing edge can be added while retaining the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_superset_of_hereditary__p2m_ff3915fc_abca_4176_9ba9_489c8aaa0e6f_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V},
      (∀ u v, G.Adj u v → H.Adj u v) → P H → P G)
    (S : SimpleGraph V) (hS : P S) :
    ∃ T : SimpleGraph V,
      (∀ u v, S.Adj u v → T.Adj u v) ∧
      P T ∧
      (∀ u v, u ≠ v → ¬ T.Adj u v →
        ¬ ∃ U : SimpleGraph V,
          (∀ x y, T.Adj x y → U.Adj x y) ∧
          P U ∧ U.Adj u v) := by sorry
