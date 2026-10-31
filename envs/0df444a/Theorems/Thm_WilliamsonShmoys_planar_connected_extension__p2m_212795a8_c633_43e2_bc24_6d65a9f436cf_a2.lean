-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
-- name    : WilliamsonShmoys.planar_connected_extension__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:12:56.103771+00:00
-- url     : https://prove2.me/theorems/6ace8332-1aee-435e-952c-c9d3858532a8
-- title:
--   Connected drawable extension preserving vertices and edge count
-- statement:
--   A drawable finite simple graph on at least three vertices has a connected drawable supergraph on the same vertices with at least as many edges. The vertex-count hypothesis is inherited from the parent; connecting components by arcs in the complement of the finite drawing preserves the existing drawing and adds edges without crossings. This removes disconnectedness from the parent’s edge-bound argument. The remaining work is formalizing the component-joining construction for the given drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_extension__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by sorry
