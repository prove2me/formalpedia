-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_component_support_restrict_4db24ad1
-- name    : WilliamsonShmoys.planarDrawingOn_component_support_restrict_4db24ad1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:06:06.993839+00:00
-- url     : https://prove2.me/theorems/b14066e1-4604-48a2-905f-2b25b30df92c
-- title:
--   Restrict a planar drawing to a component support
-- statement:
--   A drawing restricts to the graph induced on any component support. The finite-type instance for the support subtype is explicit so the induced graph and drawing predicate elaborate. Restrict the vertex placement and edge-arc witnesses; injectivity, continuity, endpoints, and noncrossing are inherited.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_component_support_restrict_4db24ad1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    [Fintype (↥C.supp)] :
    HasPlanarDrawingOn (L.induce C.supp) := by sorry
