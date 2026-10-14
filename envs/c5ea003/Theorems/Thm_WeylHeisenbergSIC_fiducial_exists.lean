-- Prove2me | Theorems.Thm_WeylHeisenbergSIC_fiducial_exists
-- name    : WeylHeisenbergSIC.fiducial_exists
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:00:54.404555+00:00
-- url     : https://prove2.me/theorems/5f792a85-f487-46d2-a9b8-64fc98c1b4c2
-- title:
--   Weyl-Heisenberg SIC fiducial existence in every positive dimension
-- statement:
--   For every positive integer d, there exists a normalized complex vector psi indexed by Z/dZ such that every nonidentity Weyl-Heisenberg displacement has squared overlap 1/(d+1) with psi. Explicitly, the displacement (a,b) sends psi(x) to exp(2*pi*i*b*x/d) times psi(x+a). This is the group-covariant SIC existence conjecture, a stronger sufficient statement for the SIC-POVM mission. It is left OPEN: the orbit-construction proof does not establish this existence claim. The dimension-one displacement condition is vacuous.
-- source:
--   Renes, Blume-Kohout, Scott and Caves, Symmetric Informationally Complete Quantum Measurements, J. Math. Phys. 45, 2171 (2004), https://arxiv.org/abs/quant-ph/0310075, Conjecture 1 and Section III. We use a phase-free displacement convention: shift x by a and multiply by exp(2*pi*i*b*x/d). Global unit phases do not affect squared overlaps.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem WeylHeisenbergSIC.fiducial_exists (d : ℕ) [NeZero d] :
    ∃ ψ : ZMod d → ℂ,
      (∑ x : ZMod d, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod d, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod d, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹ := by sorry
