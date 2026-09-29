-- Prove2me | solution 1 for MeanFieldPhaseTransition.tanh_ge_cubic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:38:31.591934+00:00
-- url     : https://prove2.me/submissions/4beeec91-e43a-494a-a3f0-1566848bc6c8

-- Sol generated from Novelty/MeanFieldPhaseTransition.lean
import Mathlib
import Definitions.Def_Novelty_MeanFieldPhaseTransition
import Theorems.Thm_MeanFieldPhaseTransition_tanh_lt_self

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


/-- `tanh` is nonnegative on the nonnegative axis. -/
theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply div_nonneg _ (Real.cosh_pos x).le
  rw [← Real.sinh_zero]; exact Real.sinh_le_sinh.mpr hx


/-! ### The order parameter (spontaneous magnetization) -/





/-! ### Disordered phase: uniqueness of `m = 0` for `β ≤ 1` -/


/-! ### Ordered phase: existence of nonzero magnetization for `β > 1` -/


/-! ### Second-order onset with mean-field critical exponent `1/2` -/



open MeanFieldPhaseTransition in
theorem solution{x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.tanh x := by
  have key : MonotoneOn (fun t => Real.tanh t - (t - t ^ 3 / 3)) (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_tanh.sub (by fun_prop)).continuousOn
    · exact (differentiable_tanh.sub (by fun_prop)).differentiableOn
    · intro t ht
      simp only [interior_Ici, Set.mem_Ioi] at ht
      have hd : HasDerivAt (fun t => Real.tanh t - (t - t ^ 3 / 3))
          ((1 - Real.tanh t ^ 2) - (1 - 3 * t ^ 2 / 3)) t := by
        have h1 := hasDerivAt_tanh t
        have h2 : HasDerivAt (fun t : ℝ => t - t ^ 3 / 3) (1 - 3 * t ^ 2 / 3) t := by
          have := (hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)
          convert this using 1
        exact h1.sub h2
      rw [hd.deriv]
      have htt : Real.tanh t ≤ t := (tanh_lt_self ht).le
      have htn : 0 ≤ Real.tanh t := tanh_nonneg ht.le
      nlinarith [htt, htn, ht.le]
  have := key Set.self_mem_Ici (Set.mem_Ici.mpr hx) hx
  simp at this; linarith
