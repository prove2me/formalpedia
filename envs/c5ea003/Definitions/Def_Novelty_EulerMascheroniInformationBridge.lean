-- Prove2me | Definitions.Def_Novelty_EulerMascheroniInformationBridge
-- name    : Novelty_EulerMascheroniInformationBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:24:49.352987+00:00
-- url     : https://prove2.me/theorems/5558a141-f5d5-45ec-a703-bbadb8ac7d79
-- title:
--   Aether Catalog definitions — Novelty_EulerMascheroniInformationBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EulerMascheroniInformationBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EulerMascheroniInformationBridge.lean by skeleton subtraction
import Mathlib

/-!
# Euler–Mascheroni constant as accumulated information divergence

This file connects analytic number theory with information theory.  For positive
rates `λ` and `μ`, the Kullback–Leibler divergence from an exponential law of rate
`λ` to one of rate `μ` has the closed form

`log (λ / μ) + μ / λ - 1`.

At the consecutive integer rates `λ = k+1`, `μ = k+2`, this is exactly the
`k`-th nonnegative summand in the classical series for the Euler–Mascheroni
constant.  Consequently, `γ` is the accumulated KL divergence along the chain
of exponential distributions with rates `1, 2, 3, ...`.
-/

open Real Filter Finset Topology

namespace EulerMascheroniInformationBridge

/-- The classical nonnegative summand whose sum is `γ`. -/
noncomputable def gammaTerm (k : ℕ) : ℝ :=
  1 / (k + 1 : ℝ) - Real.log ((k + 2) / (k + 1))






/-- Closed form of `D_KL(Exp(λ) ‖ Exp(μ))` for exponential distributions.
The definition is algebraic so the bridge does not depend on a particular
measure-theoretic encoding of probability distributions. -/
noncomputable def exponentialKL (rate₁ rate₂ : ℝ) : ℝ :=
  Real.log (rate₁ / rate₂) + rate₂ / rate₁ - 1







end EulerMascheroniInformationBridge


