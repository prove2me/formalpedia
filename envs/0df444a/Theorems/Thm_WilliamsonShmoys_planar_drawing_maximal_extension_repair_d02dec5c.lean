-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_repair_d02dec5c
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_repair_d02dec5c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:57:42.66108+00:00
-- url     : https://prove2.me/theorems/5ea1c26e-47eb-4468-99c6-c89a274ea15f
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_repair_d02dec5c
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNplanar : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
        (forall L : SimpleGraph V, K <= L ->
          WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) := by sorry
