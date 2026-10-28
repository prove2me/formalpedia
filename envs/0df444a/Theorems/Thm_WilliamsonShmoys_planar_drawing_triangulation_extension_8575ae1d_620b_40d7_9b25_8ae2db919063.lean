-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_8575ae1d_620b_40d7_9b25_8ae2db919063
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_8575ae1d_620b_40d7_9b25_8ae2db919063
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:21:48.681465+00:00
-- url     : https://prove2.me/theorems/f2db904c-5721-454a-bbac-7987a5a61819
-- title:
--   Triangulating a connected planar drawing
-- statement:
--   Extend the given connected planar graph, without adding vertices, to a connected planar graph attaining the triangulated planar edge count. The lower bound of three vertices is retained for the planar triangulation formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_8575ae1d_620b_40d7_9b25_8ae2db919063
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hQconn : Q.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.Connected ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
