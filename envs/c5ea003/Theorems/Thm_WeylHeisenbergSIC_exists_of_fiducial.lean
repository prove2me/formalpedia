-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_exists_of_fiducial
-- name    : WeylHeisenbergSIC.exists_of_fiducial
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:00:54.650366+00:00
-- url     : https://prove2.me/theorems/6d4cd55d-066e-44d7-ad10-8f83c044a144
-- title:
--   A Weyl-Heisenberg fiducial generates a SIC vector family
-- statement:
--   For any positive dimension d, suppose a function psi on Z/dZ has squared norm one and its overlap with each nonidentity cyclic shift-and-phase displacement has squared modulus 1/(d+1). Its d squared displaced copies form a family of d squared unit vectors in C^d with that same squared overlap between every distinct pair. The conclusion uses exactly the vector-family formulation of the SIC-POVM mission. No claim of fiducial existence is made by this implication.
-- source:
--   Renes, Blume-Kohout, Scott and Caves, Symmetric Informationally Complete Quantum Measurements, J. Math. Phys. 45, 2171 (2004), https://arxiv.org/abs/quant-ph/0310075, Conjecture 1 and Section III. We use a phase-free displacement convention: shift x by a and multiply by exp(2*pi*i*b*x/d). Global unit phases do not affect squared overlaps.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.exists_of_fiducial (d : ℕ) [NeZero d] (ψ : ZMod d → ℂ)
    (hnorm : (∑ x : ZMod d, Complex.normSq (ψ x)) = 1)
    (hfid : ∀ a b : ZMod d, (a,b) ≠ (0,0) →
      Complex.normSq (∑ x : ZMod d, star (ψ x) *
        (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹) :
    ∃ Φ : Fin (d^2) → EuclideanSpace ℂ (Fin d),
      (∀ i, ‖Φ i‖ = 1) ∧
      Pairwise (fun i j =>
        Complex.normSq (∑ k : Fin d, star (Φ i k) * Φ j k) = (d+1 : ℝ)⁻¹) := by sorry
