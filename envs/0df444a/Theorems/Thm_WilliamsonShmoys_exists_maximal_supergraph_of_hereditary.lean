-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_hereditary
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_hereditary
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:11:16.924761+00:00
-- url     : https://prove2.me/theorems/21c67f50-7a8e-4660-869d-ce02ffa7c4e0
-- title:
--   Finite hereditary graph properties admit maximal supergraphs
-- statement:
--   For a finite vertex type, every graph satisfying a property inherited by subgraphs is contained in a supergraph satisfying that property which is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_hereditary
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hHereditary : ∀ G H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet → P H → P G)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      P L ∧
      ∀ M : SimpleGraph V,
        Set.Subset L.edgeSet M.edgeSet →
        P M →
        M.edgeSet = L.edgeSet := by sorry
