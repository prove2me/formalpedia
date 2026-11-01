-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:46.661205+00:00
-- url     : https://prove2.me/theorems/8e1589da-8236-4d2f-a43b-c94137df9ddf
-- title:
--   Connected planar supergraph extension
-- statement:
--   This new lemma removes disconnected-component handling from the Euler step. For any finite vertex type, including types with zero, one, or two vertices, a drawing can be extended by repeatedly joining distinct components with an arc in the complement of the existing finite drawing. Since the new edge joins distinct components, it was not already an edge. The remaining proof is the topological construction of such an arc while preserving the drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
