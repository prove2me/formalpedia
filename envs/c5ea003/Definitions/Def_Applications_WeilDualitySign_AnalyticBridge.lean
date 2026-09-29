-- Prove2me | Definitions.Def_Applications_WeilDualitySign_AnalyticBridge
-- name    : Applications_WeilDualitySign_AnalyticBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:58:50.011388+00:00
-- url     : https://prove2.me/theorems/64b600ee-ac3e-4571-b63b-835506cadd19
-- title:
--   Aether Catalog definitions — Applications_WeilDualitySign_AnalyticBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.WeilDualitySign.AnalyticBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/WeilDualitySign/AnalyticBridge.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_BSD_FunctionalEquation
import Definitions.Def_Applications_WeilDualitySign_CentralParity
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cycle 4: from Frobenius eigenvalues to the analytic parity theorem

Cycles 1–3 are algebra: a duality eigensystem `(Q, α, σ)` has functional-equation sign
`ε = (−1)^{d + #neg-fixed} = (−1)^{m₊}`.  `Catalog/Applications/BSD/FunctionalEquation.lean`
is analysis: any function `Λ` analytic at the central point with
`Λ(2 − s) = w · Λ(s)` satisfies `(−1)^{ord_{s=1} Λ} = w`.

This file **joins the two**.  Writing `Q = e^L` (any complex logarithm of the weight) and
substituting `T = e^{−sL}` — under which the duality substitution `T ↦ (Q²T)⁻¹` becomes
exactly the reflection `s ↦ 2 − s`, with the central point `T = Q⁻¹` at `s = 1` — the
completed function

  `Λ_E(s) = e^{(s−1)·d·L/2} · P(e^{−sL})`

is entire and satisfies `Λ_E(2 − s) = ε · Λ_E(s)` (`completedL_functional_equation`).
Feeding this into the analytic parity theorem yields

  `(−1)^{ord_{s=1} Λ_E} = ε = (−1)^{m₊}`,

so the **analytic order of vanishing at the central point has the same parity as the
multiplicity of the eigenvalue `q^{n/2}`** (`analyticRank_parity_eq_centralOrder`), and
under the mission hypothesis it has the parity of the degree
(`analyticRank_parity_of_no_neg_fixed`).  The finite-field combinatorics and the
archimedean Taylor symmetry are two computations of the same `ℤ/2`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the exponential substitution should turn the polynomial
  functional equation into the analytic one *exactly*, with the `Q^d`-factor absorbed
  into the half-power `e^{(s−1)dL/2}` — the eigenvalue-model avatar of the conductor
  factor `N^{s/2}` in the completed Hasse–Weil `Λ`.
Experiment (Experimenter): the exponent bookkeeping is
  `(1−s)d/2 + d − (2−s)d = (s−1)d/2`; everything else is `Complex.exp_add` and the
  cycle-1 identity applied at `T = e^{−sL}` (nonzero because `exp` never vanishes).
Analysis (Analyst): only *one* hypothesis of the analytic theorem is not automatic,
  namely `analyticOrderAt Λ 1 ≠ ⊤` (the function is not locally zero).  It is kept
  explicit rather than silently assumed; it is exactly the statement that the zeta
  factor is not the zero function, and it is discharged for the model in
  `completedL_ne_zero_of_charPoly_ne_zero`.
Critique (Critic): the logarithm `L` is a *choice*; different branches change `Λ_E` by a
  factor `e^{2πik(s−1)d/2}`, which is nowhere zero, so the order of vanishing — and
  hence the parity conclusion — is independent of that choice.  Nothing in the argument
  needs `Q` real or positive, so the bridge applies to any weight.
-/

open Finset

namespace WeilDualitySign

namespace DualEigensystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : DualEigensystem ℂ ι) (L : ℂ)

/-- The **completed L-function of a duality eigensystem**, in the variable `s` obtained
from `T` by `T = e^{−sL}` (where `e^L = Q`):

  `Λ_E(s) = e^{(s−1)·d·L/2} · P(e^{−sL})`.

The prefactor is the eigenvalue-model analogue of the conductor factor `N^{s/2}` in the
completed Hasse–Weil L-function. -/
noncomputable def completedL : ℂ → ℂ := fun s =>
  Complex.exp (((s - 1) * E.deg / 2) * L) * E.charPoly (Complex.exp (-s * L))








end DualEigensystem

end WeilDualitySign


