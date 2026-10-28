-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_d839d705_6fcc_4c88_b277_9f84682e1a8e
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_d839d705_6fcc_4c88_b277_9f84682e1a8e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:08:21.995681+00:00
-- url     : https://prove2.me/theorems/f4391944-86eb-4eac-a7f3-ae1c9283175a
-- title:
--   Existence of an inclusion-maximal planar extension
-- statement:
--   Every finite planar graph has a planar supergraph on the same vertex type that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension_d839d705_6fcc_4c88_b277_9f84682e1a8e
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
