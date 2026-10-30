-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraphs__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
-- name    : WilliamsonShmoys.finite_drawable_supergraphs__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:53.882745+00:00
-- url     : https://prove2.me/theorems/cb53f354-fccf-4552-b0a8-00c79a7fdb8c
-- title:
--   Finite family of drawable supergraphs
-- statement:
--   For a finite ordered vertex type, the set of drawable simple graphs containing a fixed graph is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.finite_drawable_supergraphs__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) : ({T : SimpleGraph V | L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T}).Finite := by sorry
