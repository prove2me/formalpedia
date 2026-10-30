-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_4a772063d306_45bd_a029_619aef07cba4_a11
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_4a772063d306_45bd_a029_619aef07cba4_a11
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:02:29.23278+00:00
-- url     : https://prove2.me/theorems/9842fcfb-c92b-479b-852c-c8ab762911dc
-- title:
--   Extend a planar drawing to a connected supergraph
-- statement:
--   A finite graph drawn without crossings and with at least three vertices admits a connected planar supergraph on the same vertex type. This isolates the component-joining step; an independent route constructs noncrossing arcs between distinct components in the complement of the finite drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_4a772063d306_45bd_a029_619aef07cba4_a11
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V, T ≤ S ∧ S.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn S := by
  sorry
