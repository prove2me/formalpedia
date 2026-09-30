-- Prove2me | Theorems.Thm_XuMannorRobust_Standard_theorem1_robust_generalization_bound
-- name    : XuMannorRobust.Standard.theorem1_robust_generalization_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:39:56.994061+00:00
-- url     : https://prove2.me/theorems/47031df9-99ef-4d25-b2a6-700c841e8b86
-- title:
--   Theorem 1: a $(K,\epsilon(\cdot))$-robust algorithm has $|\mathcal L(\mathcal A_s) - l_{\mathrm{emp}}(\mathcal A_s)| \le \epsilon(s) + M\sqrt{(2K\ln 2 + 2\ln(1/\delta))/n}$ w.p. $\ge 1-\delta$
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathcal Z$, $\mathcal H$ a set of hypotheses and $l : \mathcal H \times \mathcal Z \to \mathbb R$ a loss with $0 \le l(h,z) \le M$ for all $h, z$ and $l(h, \cdot)$ measurable for every $h$. Let $n \ge 1$ and let $\mathcal A : \mathcal Z^n \to \mathcal H$ be a learning algorithm that is $(K, \epsilon(\cdot))$-robust (Definition 2). Let the training set $\mathbf s$ consist of $n$ i.i.d. draws from $\mu$. Then for every $\delta > 0$, with probability at least $1 - \delta$,
--
--   $$|\mathcal L(\mathcal A_{\mathbf s}) - l_{\mathrm{emp}}(\mathcal A_{\mathbf s})| \le \epsilon(\mathbf s) + M \sqrt{\frac{2K\ln 2 + 2\ln(1/\delta)}{n}},$$
--
--   where $\mathcal L(\mathcal A_{\mathbf s}) = \mathbb E_{z\sim\mu}\, l(\mathcal A_{\mathbf s}, z)$ is the expected error and $l_{\mathrm{emp}}(\mathcal A_{\mathbf s}) = \frac1n\sum_{i=1}^n l(\mathcal A_{\mathbf s}, s_i)$ the training error.
--
--   This is the main generalization bound of Xu and Mannor's robustness framework: an algorithm whose loss varies by at most $\epsilon(\mathbf s)$ within each cell of a fixed partition of the sample space into $K$ cells generalizes, with a complexity term depending only on $K$ and not on the hypothesis class.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: the outer measure under $\mu^n$ (on `Fin n → Z`) of the set of training sets violating the inequality is at most $\delta$; this requires no measurability of $\mathbf s \mapsto \mathcal A_{\mathbf s}$. Measurability of $l(h,\cdot)$ and of the partition cells is added to the paper's model, which ignores measurability. $n \ge 1$ is assumed (the paper's "n IID draws"); at $n = 0$ Lean's $1/0 = 0$ would make the claim false. For $\delta > 2^K$ the radicand is negative and the square root is $0$; the statement stays true there.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 396, Theorem 1

import Mathlib
import Definitions.Def_XuMannorRobust_Standard_Losses
import Definitions.Def_XuMannorRobust_Standard_IsRobust

open MeasureTheory

namespace XuMannorRobust.Standard

/-- **Theorem 1** (Xu & Mannor 2012, p. 396). If the learning algorithm `A` is
`(K, ε(·))`-robust, the loss takes values in `[0, M]` (and each `l h` is measurable), and the
training set `s` consists of `n ≥ 1` i.i.d. draws from the probability measure `μ`, then for every
`δ > 0`, with probability at least `1 − δ`,
`|𝓛(A_s) − l_emp(A_s)| ≤ ε(s) + M √((2K ln 2 + 2 ln(1/δ))/n)`: the outer measure under `μⁿ` of
the set of training sets where this fails is at most `δ`. -/
theorem theorem1_robust_generalization_bound {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ) (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    (hl_meas : ∀ h, Measurable (l h)) {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H) (K : ℕ)
    (ε : (Fin n → Z) → ℝ) (hA : IsRobust l A K ε) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => μ)
        {s | ¬ (|expectedLoss μ l (A s) - empiricalLoss l (A s) s|
            ≤ ε s + M * Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))}
      ≤ ENNReal.ofReal δ := by sorry

end XuMannorRobust.Standard
