-- Prove2me | Theorems.Thm_wiener_atom_sq_le_cesaro_measurable
-- name    : wiener_atom_sq_le_cesaro_measurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T11:25:13.711362+00:00
-- url     : https://prove2.me/theorems/56c48a2c-d708-4076-8c73-b64dc2428403
-- title:
--   Wiener bound for a measurable random variable: atom squared vs Cesaro mean of |chf|^2
-- statement:
--   For a measurable real random variable $Z$ on a probability space, the squared atom $P(Z = x)^2$ is at most the Cesaro mean over $[0,U]$ of $|\hat\mu(u)|^2$ (written as $(\int \cos(uZ))^2 + (\int \sin(uZ))^2$) plus $\varepsilon$, for all large $U$. This is Wiener's theorem on atoms of a measure via its characteristic function.
-- source:
--   Wiener's theorem (Wiener 1933); cf. Kyprianou, Fluctuations of Levy Processes, Thm 5.4 proof infrastructure

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Wiener's theorem for an arbitrary measurable real random variable: the squared atom at x is bounded by the Cesaro mean of |chf|^2 plus epsilon. -/
theorem wiener_atom_sq_le_cesaro_measurable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Omega → Real) (hZ : Measurable Z) :
  ∀ x : Real, ∀ ε : ENNReal, 0 < ε →
    ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
      (P {omega : Omega | Z omega = x})^2 ≤
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫ omega, Real.cos (u * Z omega) ∂P)^2 + (∫ omega, Real.sin (u * Z omega) ∂P)^2) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε := by
  sorry
