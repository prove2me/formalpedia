-- Prove2me | Definitions.Def_Applications_IsingModel_Peierls
-- name    : Applications_IsingModel_Peierls
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:14.417888+00:00
-- url     : https://prove2.me/theorems/e77d7b2c-1161-4ed4-bb70-e0d8f8d71ee5
-- title:
--   Aether Catalog definitions — Applications_IsingModel_Peierls
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.IsingModel.Peierls`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/IsingModel/Peierls.lean by skeleton subtraction
import Mathlib

/-!
# 2D Ising Model: The Peierls Argument (analytic core)

The Peierls argument proves spontaneous magnetization of the 2D Ising model at
low temperature by bounding the probability that the spin at the origin is flipped
against the boundary condition.  That probability is dominated by a sum over
*contours* (Peierls contours) `γ` enclosing the origin, each weighted by
`e^{-2β|γ|}`.  The number of contours of length `L` enclosing a fixed site is at
most `L · 3^{L}`, so the misalignment probability is dominated by the
**Peierls majorant**
`P(β) = ∑_{L} L · (3 e^{-2β})^{L}`.
When `P(β) < 1/2`, the origin spin keeps its boundary value with probability
`> 1/2`, giving spontaneous magnetization.  Here we formalize the analytic heart:
convergence of `P(β)`, its closed form, and the existence of a low-temperature
threshold `β₀` beyond which `P(β) < 1/2`.

-- !-- Lab Notes -- !--
* **Hypothesis.** The contour majorant `P(β) = ∑_L L (3e^{-2β})^L` converges for
  `3 e^{-2β} < 1` and tends to `0` as `β → ∞`, so a Peierls threshold exists.
* **Experiment.** Set `x = 3 e^{-2β}`. Use `tsum_coe_mul_geometric_of_norm_lt_one`
  to get `∑ L·x^L = x/(1-x)^2`, and `summable_pow_mul_geometric_of_norm_lt_one`
  (with `k = 1`) for convergence. For the threshold pick `β₀ = ½ log 12`, so
  `x ≤ 1/4`, whence `2x < (1-x)^2 ⇔ 0 < 1 - 4x + x^2`, giving `P < 1/2`.
* **Analysis.** Survives. The geometric closed form is exact; the threshold is a
  concrete, checkable inequality reducing to `0 < 1 - 4x + x^2` for `x ≤ 1/4`.
  The full lattice-probabilistic statement (defining contours and the Peierls
  coupling) is *true but hard* and is left to the geometry layer — the analytic
  obstruction (this series) is what controls the phase transition, and it is
  fully discharged here with 0 sorries.
* **Critique.** Not trivial: requires `Summable`/`tsum` machinery, `norm`
  estimates and a genuine inequality chain (`div_lt_iff₀`, `nlinarith`). The
  threshold is existential but *witnessed* (`β₀ = ½ log 12`), avoiding vacuity.
* **Synthesis.** Low temperature ⇒ `P(β) < 1/2` ⇒ Peierls criterion for
  spontaneous magnetization holds.
-/

namespace Ising

open Real

/-- The Peierls contour majorant `P(β) = ∑_{L} L · (3 e^{-2β})^{L}`. -/
noncomputable def peierlsBound (β : ℝ) : ℝ :=
  ∑' L : ℕ, (L : ℝ) * (3 * Real.exp (-2 * β)) ^ L








end Ising


