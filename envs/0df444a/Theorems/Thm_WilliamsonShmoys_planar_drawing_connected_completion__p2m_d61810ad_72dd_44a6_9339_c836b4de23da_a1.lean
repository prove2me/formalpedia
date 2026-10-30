-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_completion__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:25.49791+00:00
-- url     : https://prove2.me/theorems/9c676d6c-6d6d-407a-ad73-9f103d372166
-- title:
--   Connected completion of a planar drawing
-- statement:
--   A finite drawn simple graph on at least three vertices has a connected drawn simple supergraph on the same vertices, with no fewer edges. This removes disconnectedness from the parent by reducing it to the connected edge-bound child. A proof route connects components through faces while preserving the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_completion__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLplanar : HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, L ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧ L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
