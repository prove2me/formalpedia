-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_strict_extension_of_disconnected_drawing__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
-- name    : WilliamsonShmoys.planar_strict_extension_of_disconnected_drawing__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:10:37.527615+00:00
-- url     : https://prove2.me/theorems/0bc9c97a-babf-49ce-aa25-e06a76bb47e2
-- title:
--   Strict planar extension of a disconnected drawing
-- statement:
--   A disconnected graph on the given nonempty finite vertex type with a planar drawing has a strictly larger planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_strict_extension_of_disconnected_drawing__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hdisc : Not G.Connected) :
    Exists fun K : SimpleGraph V => And (LE.le G K) (And (Not (G = K)) (HasPlanarDrawingOn K)) := by sorry
