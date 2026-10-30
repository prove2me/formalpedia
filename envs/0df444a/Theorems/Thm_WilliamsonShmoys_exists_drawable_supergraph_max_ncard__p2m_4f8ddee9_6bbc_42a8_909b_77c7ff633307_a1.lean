-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_ncard__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
-- name    : WilliamsonShmoys.exists_drawable_supergraph_max_ncard__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:42.215679+00:00
-- url     : https://prove2.me/theorems/b9802bf2-846b-43c8-98b5-8e8718bf6f30
-- title:
--   Drawable supergraph maximizing edge count
-- statement:
--   Among the drawable supergraphs of K, there is one whose finite edge set has maximum cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_supergraph_max_ncard__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        K ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
