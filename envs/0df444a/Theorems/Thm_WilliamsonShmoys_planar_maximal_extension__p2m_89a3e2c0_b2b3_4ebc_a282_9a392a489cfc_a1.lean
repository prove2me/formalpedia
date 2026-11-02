-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:05:25.216206+00:00
-- url     : https://prove2.me/theorems/d50bd5f9-430a-4ac6-90e0-7716421734c3
-- title:
--   Finite maximal planar extension
-- statement:
--   Every finite drawable graph has a planar supergraph on the same vertices that has no strict planar supergraph on those vertices. Finiteness of the set of simple graphs gives an independent proof route by maximizing edge count among drawable supergraphs containing H; the vertex-count hypothesis is preserved for the next step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L <= K := by
  sorry
