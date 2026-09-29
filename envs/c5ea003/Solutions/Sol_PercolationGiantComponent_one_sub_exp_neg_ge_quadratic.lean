-- Prove2me | solution 1 for PercolationGiantComponent.one_sub_exp_neg_ge_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:16:20.59234+00:00
-- url     : https://prove2.me/submissions/9aca7b49-d7dc-40cf-ad6f-13912ca5ba27

-- Sol generated from Novelty/PercolationGiantComponent.lean
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



/-! ### The order parameter (survival probability / giant-component fraction) -/




/-! ### Subcritical regime: only the trivial solution for `λ ≤ 1` -/


/-! ### Supercritical regime: emergence of a giant component for `λ > 1` -/


/-! ### Continuous onset with mean-field percolation exponent `1` -/



open PercolationGiantComponent in
theorem solution{x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ 1 - Real.exp (-x) := by
  have key : MonotoneOn (fun t => (1 - t + t ^ 2 / 2) - Real.exp (-t)) (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · apply Differentiable.differentiableOn; fun_prop
    · intro t ht
      simp only [interior_Ici, Set.mem_Ioi] at ht
      have hd : HasDerivAt (fun t => (1 - t + t ^ 2 / 2) - Real.exp (-t))
          ((-1 + 2 * t / 2) - Real.exp (-t) * (-1)) t := by
        have h1 : HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2) (-1 + 2 * t / 2) t := by
          have := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
            ((hasDerivAt_pow 2 t).div_const 2)
          convert this using 1; push_cast; ring
        have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-t) * (-1)) t :=
          (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
        exact h1.sub h2
      rw [hd.deriv]
      have := Real.add_one_le_exp (-t)
      nlinarith [this]
  have := key Set.self_mem_Ici (Set.mem_Ici.mpr hx) hx
  simp at this; linarith
