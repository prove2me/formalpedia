-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_component_support_restrict_937ee64a84854eee
-- name    : WilliamsonShmoys.planarDrawingOn_component_support_restrict_937ee64a84854eee
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:30:54.20347+00:00
-- url     : https://prove2.me/theorems/4b70c3d9-f60d-43d3-ad3b-1a157ee6198a
-- title:
--   Restrict a planar drawing to a component support
-- statement:
--   A drawing of a graph restricts to a drawing of the graph induced on any component support. Restrict the vertex placement and retain the arcs for induced edges; injectivity, endpoint conditions, continuity, and noncrossing are inherited. The component’s finite support instance is explicit in the statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_component_support_restrict_937ee64a84854eee
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    [Fintype (↑C.supp)] :
    HasPlanarDrawingOn (L.induce C.supp) := by sorry
