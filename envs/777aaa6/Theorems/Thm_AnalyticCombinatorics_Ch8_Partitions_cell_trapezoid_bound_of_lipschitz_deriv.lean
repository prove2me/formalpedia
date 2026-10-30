-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_cell_trapezoid_bound_of_lipschitz_deriv
-- name    : AnalyticCombinatorics.Ch8.Partitions.cell_trapezoid_bound_of_lipschitz_deriv
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:30:35.444754+00:00
-- url     : https://prove2.me/theorems/9c6ecf27-cb72-46f3-b750-b762502808ab
-- title:
--   A conditional trapezoid-cell estimate from a Lipschitz derivative
-- statement:
--   Let $g,g\prime:\mathbb R\to\mathbb R$ and $M\ge0$. Assume $g$ has derivative $g\prime(z)$ at every $z\in[0,2]$, both functions have the interval integrability properties stated below, and $|g\prime(z)-g\prime(w)|\le M|z-w|$ on $[0,2]$. For every cell with $h>0$, $a\ge0$ and $a+h\le2$, $$\left|\frac{g(a)+g(a+h)}2-\frac1h\int_a^{a+h}g(x)\,dx\right|\le Mh^2.$$ The source constant and normalized cell average are retained.
--
--   This support estimate carries the following complete literal source contract:
--
--   ```lean
--   theorem cell_trapezoid_bound_of_lipschitz_deriv
--       {g gp : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
--       (hderiv : ∀ z ∈ Set.Icc (0 : ℝ) 2, HasDerivAt g (gp z) z)
--       (hint_g : ∀ ⦃u v : ℝ⦄, 0 ≤ u → v ≤ 2 →
--           IntervalIntegrable g MeasureTheory.volume u v)
--       (hint_gp : ∀ ⦃u v : ℝ⦄, 0 ≤ u → v ≤ 2 →
--           IntervalIntegrable gp MeasureTheory.volume u v)
--       (hlip : ∀ z ∈ Set.Icc (0 : ℝ) 2, ∀ w ∈ Set.Icc (0 : ℝ) 2,
--           |gp z - gp w| ≤ M * |z - w|) :
--       ∀ ⦃a h : ℝ⦄, 0 < h → 0 ≤ a → a + h ≤ 2 →
--           |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/TrapezoidCell.lean#L150. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Per-cell trapezoid error from a Lipschitz derivative (HR constant, brick 2)

Producer for the `hcell` hypothesis of `TrapezoidEM.lean`'s summation core:
for `g` with derivative `gp` on `[0,2]` and `gp` `M`-Lipschitz there,
`|trapezoid avg - integral avg| ≤ M·h²` on every cell `[a,a+h] ⊆ [0,2]`.
(ChatGPT R4 chord-interpolation proof; non-sharp constant `M`, sufficient for the
summation brick.)
-/

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

theorem AnalyticCombinatorics.Ch8.Partitions.cell_trapezoid_bound_of_lipschitz_deriv
    {g gp : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ z ∈ Set.Icc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_g : ∀ ⦃u v : ℝ⦄, 0 ≤ u → v ≤ 2 →
        IntervalIntegrable g MeasureTheory.volume u v)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 ≤ u → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Icc (0 : ℝ) 2, ∀ w ∈ Set.Icc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|) :
    ∀ ⦃a h : ℝ⦄, 0 < h → 0 ≤ a → a + h ≤ 2 →
        |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2 := by sorry
