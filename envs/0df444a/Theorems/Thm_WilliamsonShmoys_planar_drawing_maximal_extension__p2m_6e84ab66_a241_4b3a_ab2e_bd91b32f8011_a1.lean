-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:26.225718+00:00
-- url     : https://prove2.me/theorems/7202bf9d-a814-4b20-b0a7-1713c12fe256
-- title:
--   Maximal planar extension on a fixed vertex set
-- statement:
--   Any connected graph with a crossing-free drawing on a finite ordered vertex set of size at least three has a connected planar supergraph on the same vertices that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (hconn : G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧ (∀ K : SimpleGraph V, HasPlanarDrawingOn K → H ≤ K → K ≤ H) := by sorry
