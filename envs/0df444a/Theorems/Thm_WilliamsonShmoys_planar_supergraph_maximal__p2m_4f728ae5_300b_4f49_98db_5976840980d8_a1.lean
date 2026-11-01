-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:33:43.909678+00:00
-- url     : https://prove2.me/theorems/eb256fa3-9e89-4cdb-b978-02905f819491
-- title:
--   Maximal planar supergraph on the same vertices
-- statement:
--   Every finite planar graph H on at least three vertices has a planar supergraph K on the same vertices that is maximal under planar supergraph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
