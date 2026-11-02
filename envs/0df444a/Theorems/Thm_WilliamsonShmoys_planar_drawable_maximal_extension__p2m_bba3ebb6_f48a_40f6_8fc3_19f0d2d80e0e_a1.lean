-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
-- name    : WilliamsonShmoys.planar_drawable_maximal_extension__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:20:26.966206+00:00
-- url     : https://prove2.me/theorems/dcf930d8-6139-49d2-a4ec-949d77a4881c
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion. This follows by maximizing the edge count among the finite set of drawable supergraphs. The condition n ≥ 3 is retained for compatibility with the parent, although this finite maximization step does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_extension__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V,
      G.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeFinset ⊆ L.edgeFinset →
        HasPlanarDrawingOn L →
        L.edgeFinset = K.edgeFinset := by sorry
