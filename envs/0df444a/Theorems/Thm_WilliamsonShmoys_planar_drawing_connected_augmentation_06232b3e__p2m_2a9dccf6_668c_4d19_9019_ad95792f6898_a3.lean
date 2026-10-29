-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:14:13.009362+00:00
-- url     : https://prove2.me/theorems/ae0a4a79-a73d-4cfa-8a9e-24a09f20fefd
-- title:
--   Augment a planar drawing to a connected graph without decreasing its edge count
-- statement:
--   For a finite planar drawing on at least three vertices, there is a connected planar supergraph on the same vertex type with at least as many edges. The independent route is to join drawing components through the complement, including components consisting of isolated vertices. The cardinality hypothesis ensures the empty-type obstruction to connectedness does not arise.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K ∧
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
