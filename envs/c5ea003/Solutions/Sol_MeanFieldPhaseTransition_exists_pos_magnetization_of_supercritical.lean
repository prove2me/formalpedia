-- Prove2me | solution 1 for MeanFieldPhaseTransition.exists_pos_magnetization_of_supercritical
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:39:46.795546+00:00
-- url     : https://prove2.me/submissions/c7863f95-1a59-4490-ad21-72524894d9d4

-- Sol generated from Novelty/MeanFieldPhaseTransition.lean
import Mathlib
import Definitions.Def_Novelty_MeanFieldPhaseTransition
import Theorems.Thm_MeanFieldPhaseTransition_tanh_ge_cubic

/-!
# A second-order phase transition for the mean-field (Curie–Weiss) order parameter

This file gives a fully formal, self-contained treatment of the paradigmatic
*second-order phase transition* of statistical mechanics: the spontaneous
magnetization of the mean-field Ising (Curie–Weiss) ferromagnet.

## Motivation

The research theme is *"mathematics as a phase transition"*: the idea that a
large body of interconnected results behaves like a statistical-mechanical
system, with an **order parameter** measuring global coherence that switches on
sharply once a coupling strength crosses a **critical threshold**.

The cleanest exactly-solvable model exhibiting this behaviour is mean-field
theory, where the order parameter `m` (the average magnetization / "coherence")
obeys the self-consistency equation

  `m = tanh (β m)`,

with `β` the inverse temperature (the coupling strength).  We prove rigorously
that this model has a *second-order phase transition at the critical value
`β_c = 1`*:

* **Disordered phase (`0 < β ≤ 1`).**  The only solution is `m = 0`
  (`magnetization_eq_zero_of_subcritical`).  There is no spontaneous order.
* **Ordered phase (`β > 1`).**  A nonzero solution `m > 0` appears, together with
  its mirror image `-m` (`exists_pos_magnetization_of_supercritical`,
  `IsMagnetization.neg`).  Spontaneous order emerges.
* **Continuous (second-order) onset with mean-field critical exponent `1/2`.**
  Any positive solution satisfies `3 (β - 1) / β³ ≤ m²`
  (`magnetization_sq_ge_of_supercritical`), so as `β ↓ 1` the branch bifurcates
  continuously from `0` growing like `√(β − 1)` — the hallmark of a *second*-order
  (as opposed to first-order/discontinuous) transition.

All order-parameter values are bounded: `|m| < 1` (`abs_magnetization_lt_one`).

## Main analytic tools proved here

* `hasDerivAt_tanh` : `tanh' = 1 - tanh²`.
* `tanh_lt_self` : `tanh x < x` for `x > 0` (contraction below the diagonal).
* `tanh_ge_cubic` : `x - x³/3 ≤ tanh x` for `x ≥ 0` (cubic Taylor lower bound),
  which powers both the existence result and the critical-exponent bound.
-/

open MeanFieldPhaseTransition

open Real

/-! ### Calculus of `tanh` -/

/-- The derivative of the hyperbolic tangent: `tanh' x = 1 - tanh² x`. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hfun : (fun y => Real.sinh y / Real.cosh y) = Real.tanh :=
    funext fun y => (Real.tanh_eq_sinh_div_cosh y).symm
  have h : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  rw [hfun] at h; convert h using 1
  have hc := (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh]; field_simp

/-- `tanh` is differentiable on all of `ℝ`. -/
theorem differentiable_tanh : Differentiable ℝ Real.tanh :=
  fun x => (hasDerivAt_tanh x).differentiableAt

/-- `tanh` is continuous. -/
theorem continuous_tanh : Continuous Real.tanh := differentiable_tanh.continuous

/-! ### Elementary inequalities for `tanh` -/




/-! ### The order parameter (spontaneous magnetization) -/





/-! ### Disordered phase: uniqueness of `m = 0` for `β ≤ 1` -/


/-! ### Ordered phase: existence of nonzero magnetization for `β > 1` -/


/-! ### Second-order onset with mean-field critical exponent `1/2` -/



open MeanFieldPhaseTransition in
theorem solution{β : ℝ} (hβ : 1 < β) :
    ∃ m : ℝ, 0 < m ∧ IsMagnetization β m := by
  have hβ0 : 0 < β := by linarith
  -- The continuous "residual" function.
  have hcont : Continuous (fun m => Real.tanh (β * m) - m) :=
    (continuous_tanh.comp (by fun_prop)).sub continuous_id
  -- Critical scale `c = 3(β-1)/β³ > 0` and the test point `a = √c / 2`.
  set c : ℝ := 3 * (β - 1) / β ^ 3 with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; exact div_pos (by linarith) (by positivity)
  set a : ℝ := Real.sqrt c / 2 with ha_def
  have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc_pos
  have ha_pos : 0 < a := by rw [ha_def]; exact div_pos hsqrt_pos (by norm_num)
  have ha_sq : a ^ 2 = c / 4 := by
    rw [ha_def]; rw [div_pow, Real.sq_sqrt hc_pos.le]; norm_num
  -- Lower bound at `a`: `tanh (β a) > a`.
  have hfa : 0 < Real.tanh (β * a) - a := by
    have hba : 0 ≤ β * a := by positivity
    have hcubic := tanh_ge_cubic hba
    -- tanh (β a) ≥ β a - (β a)³/3, and this exceeds a since a² = c/4 < c.
    have hlt : a < β * a - (β * a) ^ 3 / 3 := by
      have hβ3a2 : β ^ 3 * a ^ 2 = 3 * (β - 1) / 4 := by
        rw [ha_sq, hc_def]; field_simp
      have hcube : (β * a) ^ 3 = (β ^ 3 * a ^ 2) * a := by ring
      have hpos : 0 < (β - 1) * a := mul_pos (by linarith) ha_pos
      rw [hcube, hβ3a2]
      nlinarith [hpos]
    linarith [hcubic, hlt]
  -- Upper bound at `a + 1`: `tanh (β (a+1)) < a + 1`.
  have hfb : Real.tanh (β * (a + 1)) - (a + 1) < 0 := by
    have := Real.tanh_lt_one (β * (a + 1))
    linarith
  -- Intermediate value theorem on `[a, a+1]`.
  have hmem : (0 : ℝ) ∈ Set.Ioo (Real.tanh (β * (a + 1)) - (a + 1)) (Real.tanh (β * a) - a) :=
    ⟨hfb, hfa⟩
  obtain ⟨m, hm_mem, hm_eq⟩ :=
    intermediate_value_Ioo' (by linarith : a ≤ a + 1) hcont.continuousOn hmem
  refine ⟨m, ?_, ?_⟩
  · exact lt_of_lt_of_le ha_pos hm_mem.1.le
  · unfold IsMagnetization; linarith [hm_eq]
