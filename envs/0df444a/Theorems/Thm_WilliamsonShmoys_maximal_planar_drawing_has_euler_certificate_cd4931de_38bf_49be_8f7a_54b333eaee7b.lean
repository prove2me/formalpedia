-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_certificate_cd4931de_38bf_49be_8f7a_54b333eaee7b
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_certificate_cd4931de_38bf_49be_8f7a_54b333eaee7b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:13:39.928901+00:00
-- url     : https://prove2.me/theorems/d3fe441d-a75c-45cc-9bb6-7b9517918e7f
-- title:
--   Maximal drawable supergraphs satisfy the planar counts
-- statement:
--   A drawable graph maximal among drawable supergraphs of W on the same finite vertex type satisfies the Euler and triangular-incidence certificate when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_MaximalPlanarEulerCertificate

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_certificate_cd4931de_38bf_49be_8f7a_54b333eaee7b
    {V : Type} [Fintype V] [LinearOrder V]
    (W X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hWX : ∀ u v, W.Adj u v → X.Adj u v)
    (hmax : ∀ Y : SimpleGraph V, HasPlanarDrawingOn Y →
      (∀ u v, W.Adj u v → Y.Adj u v) →
      ∀ u v, Y.Adj u v → X.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    HasMaximalPlanarEulerCertificate X := by sorry
