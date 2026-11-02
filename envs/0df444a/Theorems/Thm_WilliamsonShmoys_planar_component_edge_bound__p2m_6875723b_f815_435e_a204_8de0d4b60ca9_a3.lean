-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
-- name    : WilliamsonShmoys.planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:25.319218+00:00
-- url     : https://prove2.me/theorems/278b0a4b-e4b3-4f5b-934c-d513e35b19a5
-- title:
--   Planar edge bound on each connected component
-- statement:
--   Every connected component of a finite simply drawn planar graph has at most three times its number of vertices minus three edges. Restrict the drawing to the component and apply the connected planar edge bound for components of size at least three; verify sizes one and two directly. This isolates the component-level geometric argument, which remains the main proof obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (c : K.ConnectedComponent) :
    letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
    letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
    (K.induce c.supp).edgeFinset.card ≤
      3 * Fintype.card {v : V // v ∈ c.supp} - 3 := by sorry
