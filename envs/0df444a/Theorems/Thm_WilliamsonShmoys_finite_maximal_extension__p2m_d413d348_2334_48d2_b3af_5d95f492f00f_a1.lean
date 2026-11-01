-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_d413d348_2334_48d2_b3af_5d95f492f00f_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_d413d348_2334_48d2_b3af_5d95f492f00f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:06.589767+00:00
-- url     : https://prove2.me/theorems/f67b3dc9-b649-4449-99b4-9ed77c80f8f8
-- title:
--   Finite maximal extension for downward-closed graph properties
-- statement:
--   For a simple graph on a finite vertex type, every graph satisfying a downward-closed property has an extension satisfying that property that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension__p2m_d413d348_2334_48d2_b3af_5d95f492f00f_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : P M) :
    ∃ (K : SimpleGraph V) (_hKdec : DecidableRel K.Adj),
      M ≤ K ∧ P K ∧
      ∀ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
        K ≤ L → P L → L ≤ K := by sorry
