-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:01:59.445447+00:00
-- url     : https://prove2.me/theorems/492cfad2-fa34-4065-a813-7bbe1b63897a
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Among the drawable supergraphs of G on the same finite vertex type, there is one that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
