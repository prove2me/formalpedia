-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_bfd9de26_18b5_4f80_88aa_03ffeafbf182_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_bfd9de26_18b5_4f80_88aa_03ffeafbf182_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:24.470916+00:00
-- url     : https://prove2.me/theorems/7ebd5baa-3b14-4d26-a3b1-046a38567718
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing has an inclusion-maximal planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_bfd9de26_18b5_4f80_88aa_03ffeafbf182_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ C : SimpleGraph V,
      G ≤ C ∧ WilliamsonShmoys.HasPlanarDrawingOn C ∧
      ∀ H : SimpleGraph V, C ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = C := by sorry
