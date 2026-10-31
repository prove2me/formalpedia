-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
-- name    : WilliamsonShmoys.maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:25:34.741892+00:00
-- url     : https://prove2.me/theorems/22ec19d4-3db6-4330-9c26-3c973d11bb33
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable finite graph has a supergraph on the same vertex type that is drawable and inclusion-maximal among drawable supergraphs. Prove this by maximizing edge count over the finite set of drawable supergraphs containing the input graph. This removes the augmentation step from the parent; it does not establish the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ H : SimpleGraph V, L ≤ H →
          WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L := by sorry
