-- Prove2me | solution 1 for MeanFieldPhaseTransition.tanh_lt_self
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:36:30.358282+00:00
-- url     : https://prove2.me/submissions/5ddd4152-1f08-413b-8540-48bf5ebe846f

-- Sol generated from Novelty/MeanFieldPhaseTransition.lean
import Mathlib
import Definitions.Def_Novelty_MeanFieldPhaseTransition

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




/-! ### Elementary inequalities for `tanh` -/




/-! ### The order parameter (spontaneous magnetization) -/





/-! ### Disordered phase: uniqueness of `m = 0` for `β ≤ 1` -/


/-! ### Ordered phase: existence of nonzero magnetization for `β > 1` -/


/-! ### Second-order onset with mean-field critical exponent `1/2` -/



open MeanFieldPhaseTransition in
theorem solution{x : ℝ} (hx : 0 < x) : Real.tanh x < x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos x)]
  have key : StrictMonoOn (fun t => t * Real.cosh t - Real.sinh t) (Set.Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · fun_prop
    · intro t ht
      simp only [interior_Ici, Set.mem_Ioi] at ht
      have hd : HasDerivAt (fun t => t * Real.cosh t - Real.sinh t) (t * Real.sinh t) t := by
        have := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
        convert this using 1; simp
      rw [hd.deriv]
      have : 0 < Real.sinh t := by rw [Real.sinh_pos_iff]; exact ht
      positivity
  have := key Set.self_mem_Ici (Set.mem_Ici.mpr hx.le) hx
  simp at this; linarith
