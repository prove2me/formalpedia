-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_arithmetic__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
-- name    : WilliamsonShmoys.planar_face_arithmetic__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:07:38.05208+00:00
-- url     : https://prove2.me/theorems/adcfe74c-2d52-459f-b9a5-6683ade41858
-- title:
--   Finite face certificate from the planar edge count
-- statement:
--   From the edge-count equation and the lower bound of three vertices, construct a finite index type of size $2n-4$ and give each index length three. This removes the certificate bookkeeping from the parent and can be proved independently using the finite type $\mathrm{Fin}(2n-4)$, casts, and arithmetic; the lower bound handles natural subtraction at the boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_arithmetic__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
    (n e : ℕ) (hn : 3 ≤ n) (hedge : e + 6 = 3 * n) :
    ∃ (F : Type) (_ : Fintype F) (length : F → ℕ),
      (∑ f : F, (length f : ℤ) = 2 * (e : ℤ)) ∧
      ((n : ℤ) - (e : ℤ) + (Fintype.card F : ℤ) = 2) ∧
      (∀ f : F, length f = 3) ∧
      ((∑ f : F, (length f : ℤ)) = 3 * (Fintype.card F : ℤ)) := by sorry
