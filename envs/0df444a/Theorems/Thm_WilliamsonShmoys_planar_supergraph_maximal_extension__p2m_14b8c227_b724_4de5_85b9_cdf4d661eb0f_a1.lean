-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:19.050071+00:00
-- url     : https://prove2.me/theorems/a7e40797-bbb7-4ed5-a4c8-71639bc08809
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. The finite set of possible added edges gives a concrete route: repeatedly extend the drawing whenever a further edge can be added without losing planarity, and stop when no such extension remains.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P := by sorry
