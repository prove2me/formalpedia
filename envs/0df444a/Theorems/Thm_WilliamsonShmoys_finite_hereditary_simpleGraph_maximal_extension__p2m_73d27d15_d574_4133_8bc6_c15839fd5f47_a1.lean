-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_hereditary_simpleGraph_maximal_extension__p2m_73d27d15_d574_4133_8bc6_c15839fd5f47_a1
-- name    : WilliamsonShmoys.finite_hereditary_simpleGraph_maximal_extension__p2m_73d27d15_d574_4133_8bc6_c15839fd5f47_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:16:51.880773+00:00
-- url     : https://prove2.me/theorems/3008a645-d375-4623-bd04-29d7ee9f8b89
-- title:
--   Maximal extension for a hereditary property of finite simple graphs
-- statement:
--   For a finite vertex type, every graph satisfying a property inherited by subgraphs has a supergraph maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_hereditary_simpleGraph_maximal_extension__p2m_73d27d15_d574_4133_8bc6_c15839fd5f47_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hP : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (N : SimpleGraph V) (hN : P N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by sorry
