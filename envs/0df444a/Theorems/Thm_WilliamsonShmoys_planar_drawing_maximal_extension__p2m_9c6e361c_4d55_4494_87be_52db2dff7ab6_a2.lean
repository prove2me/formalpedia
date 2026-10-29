-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_9c6e361c_4d55_4494_87be_52db2dff7ab6_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9c6e361c_4d55_4494_87be_52db2dff7ab6_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:21:12.098249+00:00
-- url     : https://prove2.me/theorems/e63f6d4c-84b2-4c27-b440-af75dc6ce627
-- title:
--   A planar drawing has a maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing has a supergraph on the same vertices that has a planar drawing and admits no strictly larger planar supergraph. The finite vertex bound is retained from the parent, though this existence step does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9c6e361c_4d55_4494_87be_52db2dff7ab6_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      (forall {u v}, H.Adj u v -> K.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      (forall L : SimpleGraph V,
        (forall {u v}, K.Adj u v -> L.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) := by sorry
