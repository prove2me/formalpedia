-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_64019286_52a7_4945_b306_7d1954508408_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_64019286_52a7_4945_b306_7d1954508408_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:30.225493+00:00
-- url     : https://prove2.me/theorems/8cfc30a7-a109-4ab3-ab69-1fa1cd3bc971
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that is maximal under inclusion among drawable graphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_64019286_52a7_4945_b306_7d1954508408_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
