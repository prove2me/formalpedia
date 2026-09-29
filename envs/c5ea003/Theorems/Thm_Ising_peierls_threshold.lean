-- Prove2me | Theorems.Thm_Ising_peierls_threshold
-- name    : Ising.peierls_threshold
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:53:25.909666+00:00
-- url     : https://prove2.me/theorems/4518fe1e-83c6-43cc-89fd-99422d5a8a32
-- title:
--   Low-temperature Peierls criterion.
-- statement:
--   **Low-temperature Peierls criterion.** There is a finite inverse-temperature
--   threshold `β₀ > 0` (witnessed by `β₀ = ½ log 12`) such that for all `β ≥ β₀` the
--   Peierls majorant is `< 1/2`; hence the misalignment probability of the origin spin
--   is `< 1/2`, establishing spontaneous magnetization at low temperature.
--
--   ```lean
--   theorem Ising.peierls_threshold:
--       ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → peierlsBound β < 1 / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/IsingModel/Peierls.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/IsingModel/Peierls.lean#L79

-- Thm stub generated from Applications/IsingModel/Peierls.lean
import Mathlib
import Definitions.Def_Applications_IsingModel_Peierls

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

open Ising

open Real

theorem Ising.peierls_threshold:
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → peierlsBound β < 1 / 2 := by sorry
