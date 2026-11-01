-- Prove2me | Theorems.Thm_finite_simpleGraph_supergraph_maximal__p2m_55be6006_4b21_4039_be32_5973123fa254_a1
-- name    : finite_simpleGraph_supergraph_maximal__p2m_55be6006_4b21_4039_be32_5973123fa254_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:40.274113+00:00
-- url     : https://prove2.me/theorems/281584af-3d21-422c-a187-500ab7f67e5d
-- title:
--   Maximal member of a finite family of graph extensions
-- statement:
--   For a finite vertex type, any property of graphs that holds for K has a supergraph satisfying that property which is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_simpleGraph_supergraph_maximal__p2m_55be6006_4b21_4039_be32_5973123fa254_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by sorry
