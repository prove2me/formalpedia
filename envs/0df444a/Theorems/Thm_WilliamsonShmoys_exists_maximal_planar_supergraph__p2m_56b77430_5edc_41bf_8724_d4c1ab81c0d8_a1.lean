-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:49.425832+00:00
-- url     : https://prove2.me/theorems/2521a354-9295-4d68-a93a-2d2a5f622a67
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under graph inclusion. The vertex-count hypothesis is retained so this child directly supplies the parent’s needed case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hMdraw : HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V => And (LE.le M N) (And (HasPlanarDrawingOn N)
      (forall K : SimpleGraph V, LE.le N K -> HasPlanarDrawingOn K -> K = N)) := by sorry
