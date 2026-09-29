-- Prove2me | Theorems.Thm_PercolationGiantComponent_one_sub_exp_neg_ge_quadratic
-- name    : PercolationGiantComponent.one_sub_exp_neg_ge_quadratic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:19:47.620792+00:00
-- url     : https://prove2.me/theorems/8588b6dd-4677-472d-b7d4-dbde2fafa3e9
-- title:
--   Quadratic Taylor lower bound: `x - x²/2 ≤ 1 - exp(-x)` for `x ≥ 0`.
-- statement:
--   Quadratic Taylor lower bound: `x - x²/2 ≤ 1 - exp(-x)` for `x ≥ 0`.  The
--   difference `(1 - x + x²/2) - exp(-x)` vanishes at `0` and has nonnegative
--   derivative `x + exp(-x) - 1 ≥ 0`, hence is monotone; rearranging gives the claim.
--
--   ```lean
--   theorem PercolationGiantComponent.one_sub_exp_neg_ge_quadratic{x : ℝ} (hx : 0 ≤ x) :
--       x - x ^ 2 / 2 ≤ 1 - Real.exp (-x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PercolationGiantComponent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PercolationGiantComponent.lean#L58

-- Thm stub generated from Novelty/PercolationGiantComponent.lean
import Mathlib
import Definitions.Def_Novelty_PercolationGiantComponent

/-!
# The percolation / giant-component phase transition (Poisson branching)

This file gives a fully formal, self-contained treatment of the **percolation
phase transition** underlying the emergence of a *giant connected component* in
the Erdős–Rényi random graph `G(n, λ/n)` and, equivalently, the survival of a
Poisson(λ) Galton–Watson branching process.

## Motivation

The research theme is *"mathematics as a phase transition"*, with the concrete
picture that a growing web of connections undergoes a **percolation transition**:
below a critical connectivity the connected clusters stay small (bounded), while
above it a single macroscopic cluster suddenly emerges.

For the mean-field percolation model the **order parameter** is the *survival
probability* (equivalently the asymptotic fraction of vertices in the giant
component) `ρ`, which satisfies the self-consistency / fixed-point equation

  `ρ = 1 - exp (-λ ρ)`,

where `λ` is the mean number of connections per vertex (the mean offspring of the
branching process).  We prove rigorously that this model has a phase transition
at the critical value `λ_c = 1`:

* **Subcritical (`0 < λ ≤ 1`).**  The only nonnegative solution is `ρ = 0`
  (`survivalProb_eq_zero_of_subcritical`): all clusters are finite, no giant
  component.
* **Supercritical (`λ > 1`).**  A solution `0 < ρ < 1` appears
  (`exists_pos_survivalProb_of_supercritical`): a giant component emerges.
* **Continuous onset with mean-field percolation exponent `1`.**  Every positive
  solution obeys `2 (λ − 1) / λ² ≤ ρ` (`survivalProb_ge_of_supercritical`), so as
  `λ ↓ 1` the giant component grows *linearly*, `ρ ≳ 2(λ − 1)` — the mean-field
  percolation critical exponent `β = 1`, in contrast with the exponent `1/2` of
  the Curie–Weiss ferromagnet.

All order-parameter values automatically lie in `[0, 1)` (`survivalProb_lt_one`).

## Main analytic tools

* `one_sub_exp_neg_lt_self` : `1 - exp(-x) < x` for `x > 0`.
* `one_sub_exp_neg_ge_quadratic` : `x - x²/2 ≤ 1 - exp(-x)` for `x ≥ 0`.
-/

open PercolationGiantComponent

open Real

/-! ### Elementary inequalities for `1 - exp(-x)` -/

theorem PercolationGiantComponent.one_sub_exp_neg_ge_quadratic{x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ 1 - Real.exp (-x) := by sorry
