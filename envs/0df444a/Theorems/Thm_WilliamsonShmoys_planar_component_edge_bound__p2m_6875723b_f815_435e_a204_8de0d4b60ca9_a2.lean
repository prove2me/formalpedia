-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a2
-- name    : WilliamsonShmoys.planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:20:56.769727+00:00
-- url     : https://prove2.me/theorems/791d10fc-01cb-4e6b-ba2b-d37e56222398
-- title:
--   Planar edge bound on each connected component
-- statement:
--   Every connected component of a finite simple graph with a crossing-free drawing has at most three times its number of vertices minus three edges. The statement installs the finite instance needed for the component vertex subtype and induced graph. For components with at least three vertices, restrict the drawing and apply the connected planar Euler bound; check sizes one and two directly. This removes the component-level geometric argument from the parent, leaving its formalization as the main open obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (c : K.ConnectedComponent) :
    letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
    letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
    (K.induce c.supp).edgeFinset.card ≤
      3 * Fintype.card {v : V // v ∈ c.supp} - 3 := by sorry
