-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
-- name    : WilliamsonShmoys.planar_connected_supergraph__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:51.922691+00:00
-- url     : https://prove2.me/theorems/f9b838b0-f6aa-487e-9e1a-71f80b7ae2c4
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   Any finite graph with a crossing-free drawing has a connected simple supergraph on the same vertex type that also has a crossing-free drawing. This removes disconnected-component bookkeeping from the parent. A proof route is to treat the finitely many disjoint embedded components as plane continua and connect them successively through the complement, routing each new arc without meeting existing edges except at its endpoints; add only edges between distinct components, so simplicity and preservation of all original edges are maintained. Isolated vertices are components and are included in the same argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
