-- Prove2me | solution 1 for PercolationGiantComponent.exists_pos_survivalProb_of_supercritical
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:17:49.641699+00:00
-- url     : https://prove2.me/submissions/f4f26068-79ad-4f19-9c20-0824eb8b469a

-- Sol generated from Novelty/PercolationGiantComponent.lean
import Mathlib
import Definitions.Def_Novelty_PercolationGiantComponent
import Theorems.Thm_PercolationGiantComponent_one_sub_exp_neg_ge_quadratic

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



/-! ### The order parameter (survival probability / giant-component fraction) -/




/-! ### Subcritical regime: only the trivial solution for `λ ≤ 1` -/


/-! ### Supercritical regime: emergence of a giant component for `λ > 1` -/


/-! ### Continuous onset with mean-field percolation exponent `1` -/



open PercolationGiantComponent in
theorem solution{lam : ℝ} (hlam : 1 < lam) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ IsSurvivalProb lam ρ := by
  have hlam0 : 0 < lam := by linarith
  -- Continuous residual function.
  have hcont : Continuous (fun ρ => (1 - Real.exp (-(lam * ρ))) - ρ) := by fun_prop
  -- Test point `a = (λ - 1) / λ²`, which satisfies `a < 2(λ-1)/λ²`.
  set a : ℝ := (lam - 1) / lam ^ 2 with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; exact div_pos (by linarith) (by positivity)
  have ha_lt1 : a < 1 := by
    rw [ha_def, div_lt_one (by positivity)]
    nlinarith [hlam0]
  -- Lower bound at `a`: `1 - exp(-λ a) > a`.
  have hfa : 0 < (1 - Real.exp (-(lam * a))) - a := by
    have hla : 0 ≤ lam * a := by positivity
    have hquad := one_sub_exp_neg_ge_quadratic hla
    -- 1 - exp(-λ a) ≥ λ a - (λ a)²/2, and this exceeds a since a = (λ-1)/λ².
    have hlt : a < lam * a - (lam * a) ^ 2 / 2 := by
      have hla_eq : lam * a = (lam - 1) / lam := by rw [ha_def]; field_simp
      rw [hla_eq, ha_def, div_lt_iff₀ (by positivity : (0:ℝ) < lam ^ 2)]
      have hrw : ((lam - 1) / lam - ((lam - 1) / lam) ^ 2 / 2) * lam ^ 2
          = (lam - 1) * lam - (lam - 1) ^ 2 / 2 := by field_simp
      rw [hrw]
      nlinarith [mul_pos (show (0:ℝ) < lam - 1 by linarith) (show (0:ℝ) < lam - 1 by linarith)]
    linarith
  -- Value at `1`: `(1 - exp(-λ)) - 1 < 0`.
  have hfb : (1 - Real.exp (-(lam * 1))) - 1 < 0 := by
    have := Real.exp_pos (-(lam * 1)); linarith
  -- Intermediate value theorem on `[a, 1]`.
  have hmem : (0 : ℝ) ∈
      Set.Ioo ((1 - Real.exp (-(lam * 1))) - 1) ((1 - Real.exp (-(lam * a))) - a) := ⟨hfb, hfa⟩
  obtain ⟨ρ, hρ_mem, hρ_eq⟩ :=
    intermediate_value_Ioo' ha_lt1.le hcont.continuousOn hmem
  refine ⟨ρ, lt_of_lt_of_le ha_pos hρ_mem.1.le, hρ_mem.2, ?_⟩
  unfold IsSurvivalProb; linarith [hρ_eq]
