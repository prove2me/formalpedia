-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_supergraph_certificate
-- name    : WilliamsonShmoys.planar_drawing_has_supergraph_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:37:38.960984+00:00
-- url     : https://prove2.me/theorems/cd4931de-38bf-49be-8f7a-54b333eaee7b
-- title:
--   Planar drawings admit certified planar supergraphs
-- statement:
--   Every drawable simple graph on at least three vertices is contained, on the same vertex set, in a drawable supergraph whose number of faces satisfies Euler’s equation and the triangular face–edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_MaximalPlanarEulerCertificate

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_supergraph_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V,
      HasPlanarDrawingOn X ∧
      (∀ u v, W.Adj u v → X.Adj u v) ∧
      HasMaximalPlanarEulerCertificate X := by sorry
