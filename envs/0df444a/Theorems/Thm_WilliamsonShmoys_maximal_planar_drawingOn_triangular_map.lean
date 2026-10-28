-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_triangular_map
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_triangular_map
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T22:46:24.46598+00:00
-- url     : https://prove2.me/theorems/87562cf2-83b3-4e5c-b3ca-0f27a2fa1d63
-- title:
--   Triangular map and face count of a maximal planar drawing
-- statement:
--   A drawing-maximal simple planar graph on at least three vertices admits an oriented triangular map whose number of faces is 2|V| − 4. The drawing hypothesis and maximality are both needed: the abstract TriangularMap structure alone does not encode that its embedding has genus zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_triangular_map
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    ∃ (m : Nat) (M : WilliamsonShmoys.TriangularMap H (Fin m)),
      2 * Fintype.card V = m + 4 := by sorry
