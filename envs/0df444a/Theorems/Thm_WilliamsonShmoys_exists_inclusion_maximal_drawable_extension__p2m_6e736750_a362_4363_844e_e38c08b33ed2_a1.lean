-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_extension__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_drawable_extension__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:51:51.85024+00:00
-- url     : https://prove2.me/theorems/d413d348-2334-48d2-b3af-5d95f492f00f
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion among drawable supergraphs. Finiteness of the possible edges gives a maximum-edge choice; the statement does not require at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_drawable_extension__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ (K : SimpleGraph V) (_hKdec : DecidableRel K.Adj),
      M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
