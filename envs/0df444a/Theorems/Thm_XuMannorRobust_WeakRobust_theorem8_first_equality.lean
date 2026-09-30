-- Prove2me | Theorems.Thm_XuMannorRobust_WeakRobust_theorem8_first_equality
-- name    : XuMannorRobust.WeakRobust.theorem8_first_equality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:53:37.265852+00:00
-- url     : https://prove2.me/theorems/77599cc4-31f4-42f5-97e4-3e1cefe72329
-- title:
--   Proof of Theorem 8 — the expected test average loss equals the expected loss
-- statement:
--   Let $\mathcal Z$ be a measurable space with a probability measure $\mu$, $\mathcal H$ a set of hypotheses, and $l : \mathcal H \times \mathcal Z \to [0, M]$ a loss measurable in its sample argument. Let $n \ge 1$ and let $\mathbf t(n) = (t_1, \dots, t_n) \sim \mu^n$ be $n$ i.i.d. samples. Then for every hypothesis $h \in \mathcal H$
--
--   $$\mathbb E_{\mathbf t(n)}\big[ L(h, \mathbf t(n)) \big] = \mathcal L(h),$$
--
--   where $L(h, \mathbf t(n)) = \frac1n \sum_{i=1}^n l(h, t_i)$ and $\mathcal L(h) = \mathbb E_{z \sim \mu} l(h, z)$.
--
--   In the proof of Theorem 8 this is applied to the fixed hypothesis $h = \mathcal A_{\mathbf s^*(n)}$, turning the generalization gap $|\mathcal L(\mathcal A_{\mathbf s^*(n)}) - L(\mathcal A_{\mathbf s^*(n)}, \mathbf s^*(n))|$ into $|\mathbb E_{\mathbf t(n)} L(\mathcal A_{\mathbf s^*(n)}, \mathbf t(n)) - L(\mathcal A_{\mathbf s^*(n)}, \mathbf s^*(n))|$.
--
--   **Formalization Note** The law of $\mathbf t(n)$ is the product measure `Measure.pi (fun _ : Fin n => μ)`. Measurability of $l(h, \cdot)$ is added (the paper ignores measurability). The case $n = 0$ is excluded, where the average loss is $0$ in Lean.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 410, proof of Theorem 8, first equality of the sufficiency display

import Mathlib
import Definitions.Def_XuMannorRobust_WeakRobust_Setup

open MeasureTheory

namespace XuMannorRobust.WeakRobust

/-- Xu & Mannor 2012, p. 410, proof of Theorem 8, first equality: since the test samples
`t(n)` are `n` i.i.d. draws from `μ`, `E_{t(n)} L(h, t(n)) = 𝓛(h)` for every hypothesis `h`
(`n ≥ 1`; loss measurable with values in `[0, M]`). -/
theorem theorem8_first_equality {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (h : H) :
    ∫ t, avgLoss l h t ∂(Measure.pi fun _ : Fin n => μ) = expectedLoss μ l h := by sorry

end XuMannorRobust.WeakRobust
