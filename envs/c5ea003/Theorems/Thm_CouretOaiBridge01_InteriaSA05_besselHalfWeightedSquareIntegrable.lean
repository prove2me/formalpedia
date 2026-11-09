-- Prove2me | Theorems.Thm_CouretOaiBridge01_InteriaSA05_besselHalfWeightedSquareIntegrable
-- name    : CouretOaiBridge01.InteriaSA05.besselHalfWeightedSquareIntegrable
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:34.598197+00:00
-- url     : https://prove2.me/theorems/981125cb-92cb-4c0f-9fb1-ae2bc895c1e7
-- title:
--   The half-parameter weighted square is integrable
-- statement:
--   For u_(1/2)(x)=x^(-1/2) and its radial weighted square W_(1/2)(x)=x u_(1/2)(x)^2, $$W_{1/2}\text{ is integrable on }(0,1).$$ This is a concrete interior case of the exact threshold.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/8a8227048f12169067627c9a591ee5448bdfc0b9/research/lean/CouretOaiBridge01/INTERIA_SA_05_BesselWeightedModes.lean#L78-L81, lines 78–81; source file SHA-256 ba27450104fa7b1723307eecdf5fd7d660e905e673981ada5da5102e73e1a042; theorem CouretOaiBridge01.InteriaSA05.besselHalfWeightedSquareIntegrable

import Definitions.Def_Couret_INTERIA_SA_05_BesselWeightedModes_d5985292a225
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import Theorems.Thm_CouretOaiBridge01_InteriaSA04_besselPowerIntegrableAtZero_iff
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

theorem besselHalfWeightedSquareIntegrable :
    IntegrableOn (besselWeightedSquare (1 / 2)) (Ioo (0 : ℝ) 1) := by sorry


end CouretOaiBridge01.InteriaSA05
