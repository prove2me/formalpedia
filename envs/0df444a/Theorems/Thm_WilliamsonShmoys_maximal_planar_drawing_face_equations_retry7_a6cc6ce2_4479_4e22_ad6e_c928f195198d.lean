-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations_retry7_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_equations_retry7_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:51:52.918746+00:00
-- url     : https://prove2.me/theorems/a9344cb4-a692-44da-95ba-6b10b58627af
-- title:
--   Euler and triangular-face equations for maximal drawings
-- statement:
--   For a drawable graph maximal among drawable supergraphs on the same finite vertex type, with at least three vertices, there is a natural face count f satisfying Euler's equation and triangular face-edge incidence counting. These equations imply the target edge count. This removes the principal topological work from the parent. At three vertices the equations give two faces and three edges; the core proof is deriving the equations from the given arc-based drawing and maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_face_equations_retry7_a6cc6ce2_4479_4e22_ad6e_c928f195198d
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, LE.le M N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> LE.le N M)
    (hCard : Nat.le 3 (Fintype.card V)) :
    Exists (fun f : Nat =>
      And (Nat.add (Fintype.card V) f = Nat.add M.edgeSet.ncard 2)
        (Nat.mul 3 f = Nat.mul 2 M.edgeSet.ncard)) := by sorry
