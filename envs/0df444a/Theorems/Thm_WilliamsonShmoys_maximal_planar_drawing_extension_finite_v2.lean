-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_finite_v2
-- name    : WilliamsonShmoys.maximal_planar_drawing_extension_finite_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:41:40.21251+00:00
-- url     : https://prove2.me/theorems/35a0306c-607f-49c7-a017-49158267505e
-- title:
--   Finite maximal planar drawing extension
-- statement:
--   Every finite graph with a planar drawing has an inclusion-maximal planar supergraph on the same vertex type. Finiteness gives a maximum among eligible supergraphs; any proper planar extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_extension_finite_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    Exists fun U : SimpleGraph V =>
      And (LE.le T U)
        (And (WilliamsonShmoys.HasPlanarDrawingOn U)
          (forall W : SimpleGraph V,
            LE.le U W -> WilliamsonShmoys.HasPlanarDrawingOn W -> W = U)) := by sorry
