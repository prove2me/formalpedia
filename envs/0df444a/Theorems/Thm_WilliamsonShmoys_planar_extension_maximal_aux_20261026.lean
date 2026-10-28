-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_aux_20261026
-- name    : WilliamsonShmoys.planar_extension_maximal_aux_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:57:19.840003+00:00
-- url     : https://prove2.me/theorems/aa96d9fb-cd8b-4896-a183-ae7dfbdfaf53
-- title:
--   Existence of a maximal planar extension on the same vertices
-- statement:
--   Every graph with a crossing-free drawing on a finite vertex type is contained in a planar graph on that same type that has no proper planar supergraph. This removes the maximal-choice step from the parent. Independently, enumerate the finitely many simple graphs on `V` that contain `H` and admit a drawing, and choose one with maximal edge count. A proper edge-set extension has strictly greater cardinality, contradicting the choice. There are no additional size or connectivity assumptions; the given drawing makes the candidate set nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_maximal_aux_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      Set.Subset H.edgeSet K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        Set.Subset K.edgeSet L.edgeSet →
        HasPlanarDrawingOn L →
        K.edgeSet = L.edgeSet := by sorry
