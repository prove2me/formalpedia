-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:23.554547+00:00
-- url     : https://prove2.me/theorems/4cee4fb6-81c0-44bc-ba4b-b191f8c55242
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every finite drawable graph has an inclusion-maximal drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  sorry
