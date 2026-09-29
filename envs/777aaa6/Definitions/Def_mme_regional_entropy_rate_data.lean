-- Prove2me | Definitions.Def_mme_regional_entropy_rate_data
-- name    : mme_regional_entropy_rate_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T20:31:12.630986+00:00
-- url     : https://prove2.me/theorems/76f4486f-e3bc-48f7-9e32-0c0d7d084d39
-- title:
--   Mass entropy and a uniform finite-alphabet entropy modulus
-- statement:
--   Define natural-log entropy, its homogeneous extension to arbitrary masses, and the supremum of entropy perturbations on the finite cube. These definitions contain no estimate or assumed entropy rate.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign. Supporting result for https://arxiv.org/html/2404.16349v2#S6 . This result alone is not the regional extraction theorem or a numerical omega certificate.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open BigOperators
open scoped Classical
set_option autoImplicit false
namespace MME.RegionRate

/-- Shannon entropy in natural-log units, allowing zero entries. -/
noncomputable def entropy {W : Type*} [Fintype W] (p : W → ℝ) : ℝ :=
  ∑ w, Real.negMulLog (p w)

/-- The homogeneous entropy of unnormalized masses. -/
noncomputable def massEntropy {W : Type*} [Fintype W] (x : W → ℝ) : ℝ :=
  entropy x - Real.negMulLog (∑ w, x w)

/-- A uniform entropy modulus on the full finite cube, including its boundary.
Its finiteness and convergence to zero are separate proved theorems. -/
noncomputable def entropyModulus (W : Type*) [Fintype W] (eps : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ p q : W → ℝ,
    (∀ w, p w ∈ Set.Icc 0 1) ∧ (∀ w, q w ∈ Set.Icc 0 1) ∧
    (∀ w, |p w - q w| ≤ eps) ∧ z = |entropy p - entropy q|}

end MME.RegionRate


