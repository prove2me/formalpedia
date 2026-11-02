-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:03.534746+00:00
-- url     : https://prove2.me/theorems/5641e734-866b-4e6a-9d69-40c2e1f45d44
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type is contained in a drawable supergraph that is maximal among drawable supergraphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K := by sorry
