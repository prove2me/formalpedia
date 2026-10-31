-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_inclusion_maximal_planar_extension__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
-- name    : WilliamsonShmoys.planar_drawing_has_inclusion_maximal_planar_extension__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:47.267081+00:00
-- url     : https://prove2.me/theorems/07b4355b-e3c1-495c-b030-8cbafb5db5d7
-- title:
--   Every finite planar drawing has an inclusion-maximal planar extension
-- statement:
--   Among drawable supergraphs of the given graph on the same finite vertex set, there is one maximal by edge inclusion. A proof can choose a candidate with the largest edge set from the finite universe of simple graphs on V; the chosen candidate remains drawable and contains M.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_inclusion_maximal_planar_extension__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet := by sorry
