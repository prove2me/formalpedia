-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:40:04.578048+00:00
-- url     : https://prove2.me/theorems/ff2c7fc5-47bb-41b0-9771-afa052fe6028
-- title:
--   Every finite planar graph has a maximal planar extension
-- statement:
--   Every graph on a finite ordered vertex type with a drawing witness has a planar supergraph on that same vertex type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
