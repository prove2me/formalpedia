-- Prove2me | Theorems.Thm_MeanFieldPhaseTransition_magnetization_eq_zero_of_subcritical
-- name    : MeanFieldPhaseTransition.magnetization_eq_zero_of_subcritical
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:07:49.673011+00:00
-- url     : https://prove2.me/theorems/2487d768-9ced-4783-9e98-d2092da6e75e
-- title:
--   Disordered phase.
-- statement:
--   **Disordered phase.**  For `0 < β ≤ 1` the only magnetization is `m = 0`:
--   no spontaneous order below the critical coupling `β_c = 1`.
--
--   ```lean
--   theorem MeanFieldPhaseTransition.magnetization_eq_zero_of_subcritical{β m : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
--       (h : IsMagnetization β m) : m = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/MeanFieldPhaseTransition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/MeanFieldPhaseTransition.lean#L145

-- Thm stub generated from Novelty/MeanFieldPhaseTransition.lean
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

theorem MeanFieldPhaseTransition.magnetization_eq_zero_of_subcritical{β m : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (h : IsMagnetization β m) : m = 0 := by sorry
