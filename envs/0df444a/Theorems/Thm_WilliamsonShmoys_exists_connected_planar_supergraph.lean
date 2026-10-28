-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph
-- name    : WilliamsonShmoys.exists_connected_planar_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:07:15.141967+00:00
-- url     : https://prove2.me/theorems/458dbfc1-0f37-4174-a918-ef7776a8f198
-- title:
--   Connected planar supergraph augmentation
-- statement:
--   A graph on at least three vertices with a crossing-free drawing has a connected supergraph on the same vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_connected_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
