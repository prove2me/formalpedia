-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_property__p2m_62c66bf3_533d_43c1_bde3_37ac00c5d3e8_a2
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_62c66bf3_533d_43c1_bde3_37ac00c5d3e8_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:35:53.479209+00:00
-- url     : https://prove2.me/theorems/f9c2944f-7a9c-40df-a54d-77f97d6a9b19
-- title:
--   Maximal supergraph satisfying a property on a finite vertex type
-- statement:
--   On a finite vertex type, any graph property satisfied by a graph L is satisfied by some supergraph of L that has no strictly larger supergraph satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_62c66bf3_533d_43c1_bde3_37ac00c5d3e8_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hL : P L) :
    ∃ K : SimpleGraph V, L ≤ K ∧ P K ∧
      (∀ H : SimpleGraph V, K ≤ H → P H → H ≤ K) := by sorry
