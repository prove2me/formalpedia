-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:57:46.580905+00:00
-- url     : https://prove2.me/theorems/5c4a3429-2a1c-4098-a0a0-aed4ca251271
-- title:
--   Existence of an inclusion-maximal planar extension
-- statement:
--   Every planar simple graph on a finite ordered vertex type has a planar supergraph on the same vertices that is inclusion-maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  sorry
