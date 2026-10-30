-- Prove2me | Theorems.Thm_finite_maximal_simpleGraph_extension__p2m_7fd45cf3_e203_47de_9dbd_2f0909dacdf1_a1
-- name    : finite_maximal_simpleGraph_extension__p2m_7fd45cf3_e203_47de_9dbd_2f0909dacdf1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:17:17.664257+00:00
-- url     : https://prove2.me/theorems/5a6aa8ac-22f1-4753-a9a2-2580049a9642
-- title:
--   Finite maximal extension among simple graphs
-- statement:
--   For a finite linearly ordered vertex type, any property of simple graphs has a maximal extension above any graph satisfying that property, where maximality is with respect to graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem finite_maximal_simpleGraph_extension__p2m_7fd45cf3_e203_47de_9dbd_2f0909dacdf1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (L : SimpleGraph V) (hP : P L) :
    ∃ M : SimpleGraph V,
      LE.le L M ∧ P M ∧
        ∀ N : SimpleGraph V, P N → LE.le M N → LE.le N M := by sorry
