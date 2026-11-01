-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_eulerFaceCertificate__p2m_266245c2_b2f6_423f_b90e_ce482fe57e00_a2
-- name    : WilliamsonShmoys.planarDrawingOn_eulerFaceCertificate__p2m_266245c2_b2f6_423f_b90e_ce482fe57e00_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:33:44.611723+00:00
-- url     : https://prove2.me/theorems/2c8e3990-9eb9-40bb-92eb-6bb9fdf833fe
-- title:
--   Euler face certificate from a planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a finite list of facial boundary walks whose count and lengths satisfy Euler’s equation, sum to twice the edge count, and are each at least three. The certificate lets the parent sum the length bounds and combine them with Euler’s equation to prove the target edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_eulerFaceCertificate__p2m_266245c2_b2f6_423f_b90e_ce482fe57e00_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (F : ℕ) (degree : Fin F → ℕ),
      Fintype.card V + F = L.edgeSet.ncard + 2 ∧
      (∑ f : Fin F, degree f) = 2 * L.edgeSet.ncard ∧
      ∀ f : Fin F, 3 ≤ degree f := by sorry
