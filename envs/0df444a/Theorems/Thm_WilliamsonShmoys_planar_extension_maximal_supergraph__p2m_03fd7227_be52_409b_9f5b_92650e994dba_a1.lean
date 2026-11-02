-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_supergraph__p2m_03fd7227_be52_409b_9f5b_92650e994dba_a1
-- name    : WilliamsonShmoys.planar_extension_maximal_supergraph__p2m_03fd7227_be52_409b_9f5b_92650e994dba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:57:56.742088+00:00
-- url     : https://prove2.me/theorems/89fd7ec5-d704-44ae-9887-a6594412388a
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that admits no proper drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_maximal_supergraph__p2m_03fd7227_be52_409b_9f5b_92650e994dba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) := by
  sorry
