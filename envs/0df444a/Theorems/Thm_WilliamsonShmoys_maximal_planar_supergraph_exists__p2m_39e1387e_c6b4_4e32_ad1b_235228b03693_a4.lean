-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:24.632863+00:00
-- url     : https://prove2.me/theorems/2d1306cb-8fa9-487e-8a52-473fb2bb2b8b
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite graph is contained in a drawable graph on the same vertices that has no strict drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by sorry
