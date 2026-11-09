-- Prove2me | Definitions.Def_Couret_INTERIA_SA_05_BesselWeightedModes_d5985292a225
-- name    : Couret_INTERIA_SA_05_BesselWeightedModes_d5985292a225
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:32.699511+00:00
-- url     : https://prove2.me/theorems/f4b429a4-1dbb-4484-a2c4-a5031ca8a3ec
-- title:
--   Singular power mode and radial weighted square
-- statement:
--   For real ν and x, defines besselSingularMode ν x=x^(−|ν|), using Lean real powers, and besselWeightedSquare ν x=x·(besselSingularMode ν x)². These are definitions of real-valued functions; on positive x they describe the singular power model and its square with radial weight x. No differential equation, operator-domain classification or boundary condition is part of these definitions.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/8a8227048f12169067627c9a591ee5448bdfc0b9/research/lean/CouretOaiBridge01/INTERIA_SA_05_BesselWeightedModes.lean; source file SHA-256 ba27450104fa7b1723307eecdf5fd7d660e905e673981ada5da5102e73e1a042

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# INTERIA-SA-05 — singular Bessel power mode and weighted norm

A first, narrowly scoped connection from the mathlib power-integrability
criterion to an explicit differentiable function.

This is a model zero-energy power mode (not a classification of the Bessel
minimal operator). In particular the logarithmic companion at ν=0, the
second-order differential equation, Weyl's alternative, boundary domains and
deficiency indices are NOT established here. No Hilbert–Pólya/RH claim.
-/

open Set MeasureTheory

namespace CouretOaiBridge01.InteriaSA05

/-- Singular model mode for Bessel's zero-energy indicial equation. -/
noncomputable def besselSingularMode (ν : ℝ) (x : ℝ) : ℝ := x ^ (-|ν|)

/-- The actual weighted square of the model mode, with radial weight `x`. -/
noncomputable def besselWeightedSquare (ν : ℝ) (x : ℝ) : ℝ :=
  x * (besselSingularMode ν x) ^ (2 : ℕ)













end CouretOaiBridge01.InteriaSA05


