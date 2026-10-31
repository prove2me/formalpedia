-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_property_maximal_extension__p2m_bb030fc9_0317_496e_aee9_1032f339651c_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_property_maximal_extension__p2m_bb030fc9_0317_496e_aee9_1032f339651c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:50.220485+00:00
-- url     : https://prove2.me/theorems/1f096b37-d454-4131-badc-49149e302369
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For any property P on simple graphs over a finite vertex type, every graph H satisfying P has a P-satisfying supergraph that is maximal among P-satisfying supergraphs under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_simpleGraph_property_maximal_extension__p2m_bb030fc9_0317_496e_aee9_1032f339651c_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ (L : SimpleGraph V), H ≤ L ∧ P L ∧
      ∀ (K : SimpleGraph V), L ≤ K → P K → K = L := by
  sorry
