-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_15067ae2_6164_4683_8340_3852ef322251_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_15067ae2_6164_4683_8340_3852ef322251_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:02.103207+00:00
-- url     : https://prove2.me/theorems/d80d0480-7eca-46ad-8d3f-07bb2fac90ce
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_15067ae2_6164_4683_8340_3852ef322251_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (N <= K)
          (∀ L : SimpleGraph V,
            WilliamsonShmoys.HasPlanarDrawingOn L → K <= L → K = L)) := by
  sorry
