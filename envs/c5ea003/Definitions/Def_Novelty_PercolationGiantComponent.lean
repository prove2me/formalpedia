-- Prove2me | Definitions.Def_Novelty_PercolationGiantComponent
-- name    : Novelty_PercolationGiantComponent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:35:14.188923+00:00
-- url     : https://prove2.me/theorems/8857fd25-ce94-4d3d-9def-6d7b16dc1d35
-- title:
--   Aether Catalog definitions — Novelty_PercolationGiantComponent
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PercolationGiantComponent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PercolationGiantComponent.lean by skeleton subtraction
import Mathlib

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

namespace PercolationGiantComponent

open Real

/-! ### Elementary inequalities for `1 - exp(-x)` -/



/-! ### The order parameter (survival probability / giant-component fraction) -/

/-- A real number `ρ` is a **survival probability** of the mean-field percolation
model at connectivity `λ` when it is a fixed point of `ρ ↦ 1 - exp(-λ ρ)`, i.e. it
solves the self-consistency equation `ρ = 1 - exp(-λ ρ)`. -/
def IsSurvivalProb (lam ρ : ℝ) : Prop := ρ = 1 - Real.exp (-(lam * ρ))



/-! ### Subcritical regime: only the trivial solution for `λ ≤ 1` -/


/-! ### Supercritical regime: emergence of a giant component for `λ > 1` -/


/-! ### Continuous onset with mean-field percolation exponent `1` -/


end PercolationGiantComponent


