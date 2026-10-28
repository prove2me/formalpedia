-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_hereditary_property
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_hereditary_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:36:21.02399+00:00
-- url     : https://prove2.me/theorems/5837b98e-5768-4e8c-8146-fddfbdcb957b
-- title:
--   Maximal supergraph for a hereditary graph property
-- statement:
--   On a finite vertex type, every graph satisfying a property preserved under taking subgraphs has a supergraph satisfying that property which is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_hereditary_property
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hher : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (U : SimpleGraph V) (hU : P U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧ P W ∧
        (∀ X : SimpleGraph V, W ≤ X → P X → X ≤ W) := by sorry
