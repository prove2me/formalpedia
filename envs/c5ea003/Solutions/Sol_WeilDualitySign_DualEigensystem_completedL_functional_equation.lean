-- Prove2me | solution 1 for WeilDualitySign.DualEigensystem.completedL_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:34.682166+00:00
-- url     : https://prove2.me/submissions/2c88b32d-b26c-4bfa-a79b-d0c4af58d693

-- Sol generated from Applications/WeilDualitySign/AnalyticBridge.lean
import Mathlib
import Definitions.Def_Applications_BSD_FunctionalEquation
import Definitions.Def_Applications_WeilDualitySign_AnalyticBridge
import Definitions.Def_Applications_WeilDualitySign_CentralParity
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
import Theorems.Thm_WeilDualitySign_DualEigensystem_charPoly_functional_equation_rootSign
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

open WeilDualitySign

open DualEigensystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : DualEigensystem ℂ ι) (L : ℂ)











open WeilDualitySign.DualEigensystem in
theorem solution(hL : Complex.exp L = E.Q) (s : ℂ) :
    E.completedL L (2 - s) = E.rootSign * E.completedL L s := by
  have hQ : E.Q ≠ 0 := E.Q_ne_zero
  have hQd : E.Q ^ E.deg ≠ 0 := pow_ne_zero _ hQ
  set T : ℂ := Complex.exp (-s * L) with hT_def
  have hT : T ≠ 0 := Complex.exp_ne_zero _
  -- the reflected variable is the duality partner of `T`
  have hrefl : E.Q ^ 2 * T = Complex.exp ((2 - s) * L) := by
    rw [hT_def, ← hL, ← Complex.exp_nat_mul, ← Complex.exp_add]
    ring_nf
  have hinv : (E.Q ^ 2 * T)⁻¹ = Complex.exp (-(2 - s) * L) := by
    rw [hrefl, ← Complex.exp_neg]
    ring_nf
  have hpow : (E.Q ^ 2 * T) ^ E.deg = Complex.exp ((2 - s) * L * E.deg) := by
    rw [hrefl, ← Complex.exp_nat_mul]
    ring_nf
  have hQpow : E.Q ^ E.deg = Complex.exp (L * E.deg) := by
    rw [← hL, ← Complex.exp_nat_mul]
    ring_nf
  -- cycle-1 functional equation at `T`
  have hfe := E.charPoly_functional_equation_rootSign T hT
  rw [hpow, hinv, hQpow] at hfe
  -- solve for `P` at the reflected point
  have hkey : E.charPoly (Complex.exp (-(2 - s) * L))
      = E.rootSign * Complex.exp (L * E.deg) * Complex.exp (-((2 - s) * L * E.deg))
        * E.charPoly T := by
    have hne : Complex.exp ((2 - s) * L * (E.deg : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hcancel : Complex.exp ((2 - s) * L * (E.deg : ℂ))
        * Complex.exp (-((2 - s) * L * (E.deg : ℂ))) = 1 := by
      rw [← Complex.exp_add]
      simp
    refine mul_left_cancel₀ hne ?_
    rw [hfe, show Complex.exp ((2 - s) * L * (E.deg : ℂ))
        * (E.rootSign * Complex.exp (L * (E.deg : ℂ))
            * Complex.exp (-((2 - s) * L * (E.deg : ℂ))) * E.charPoly T)
      = (Complex.exp ((2 - s) * L * (E.deg : ℂ))
            * Complex.exp (-((2 - s) * L * (E.deg : ℂ))))
          * (E.rootSign * Complex.exp (L * (E.deg : ℂ)) * E.charPoly T) from by ring,
      hcancel, one_mul]
  -- assemble
  simp only [completedL]
  rw [show (2 - s - 1 : ℂ) = -(s - 1) by ring, hkey, ← hT_def]
  have hexp : Complex.exp (-(s - 1) * (E.deg : ℂ) / 2 * L)
        * (Complex.exp (L * (E.deg : ℂ)) * Complex.exp (-((2 - s) * L * (E.deg : ℂ))))
      = Complex.exp ((s - 1) * (E.deg : ℂ) / 2 * L) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  linear_combination (E.rootSign * E.charPoly T) * hexp
