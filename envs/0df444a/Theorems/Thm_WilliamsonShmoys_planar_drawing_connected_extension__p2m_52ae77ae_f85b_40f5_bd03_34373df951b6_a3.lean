-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:29.709963+00:00
-- url     : https://prove2.me/theorems/c8645d84-972c-4350-854f-f6f7bdb58b09
-- title:
--   Connected planar supergraph extension for nonempty vertex types
-- statement:
--   For a finite drawn graph whose vertex type has at least three elements, there is a connected simple supergraph on the same vertices that still has a planar drawing. This cardinality condition rules out the empty-type counterexample to the earlier extension statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, K <= H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
