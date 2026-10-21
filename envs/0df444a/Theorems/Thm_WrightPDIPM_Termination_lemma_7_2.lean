-- Prove2me | Theorems.Thm_WrightPDIPM_Termination_lemma_7_2
-- name    : WrightPDIPM.Termination.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:16.635533+00:00
-- url     : https://prove2.me/theorems/63c3cc8e-d068-44c5-8038-1e18e031c96f
-- title:
--   Lemma 7.2 — the solution of min ½‖Σw‖² s.t. Hw = h satisfies ‖w̄‖ ≤ Ĉ‖h‖ uniformly in nonsingular diagonal Σ
-- statement:
--   Let $H \in \mathbb{R}^{p\times q}$. Then there is a constant $\hat C \ge 0$, depending only on $H$, such that for every $h$ in the range of $H$ and every nonsingular diagonal matrix $\Sigma$, the problem
--   $$\min_w\ \tfrac12\|\Sigma w\|^2 \quad\text{subject to}\quad Hw = h$$
--   has a unique solution $\bar w$, and
--   $$\|\bar w\| \le \hat C\,\|h\|.$$
--
--   No rank assumption is made on $H$. The lemma is used to bound $\Delta x_{\mathcal B}$ and $\Delta s_{\mathcal N}$, the components of the affine-scaling step not covered by Lemma 7.1.
--
--   **Formalization Note** $\Sigma = \operatorname{diag}(\sigma)$ with every $\sigma_j \ne 0$; $h \in \operatorname{Range}(H)$ is the existence of $w_0$ with $Hw_0 = h$. The book's phrase "the unique solution" is stated as part of the conclusion (existence and uniqueness), together with the bound for that solution. $\hat C$ is chosen before $h$ and $\Sigma$. Norms are Euclidean.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 131, Lemma 7.2 (proof p. 250)

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

namespace WrightPDIPM.Termination

open Matrix

/-- Lemma 7.2 (p. 131): for `H ∈ ℝ^{p×q}` there is a constant `Ĉ ≥ 0` depending only on `H` such
that for every `h ∈ Range(H)` and every nonsingular diagonal `Σ = diag(σ)`, the problem (7.7)
`min_w ½‖Σw‖² s.t. Hw = h` has a unique solution `w̄`, and it satisfies `‖w̄‖ ≤ Ĉ‖h‖`. -/
theorem lemma_7_2 {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) :
    ∃ Chat : ℝ, 0 ≤ Chat ∧ ∀ h : Fin p → ℝ, (∃ w₀ : Fin q → ℝ, H *ᵥ w₀ = h) →
      ∀ σ : Fin q → ℝ, (∀ j, σ j ≠ 0) →
        (∃! wbar : Fin q → ℝ, IsWLSSolution H σ h wbar) ∧
        ∀ wbar : Fin q → ℝ, IsWLSSolution H σ h wbar → norm2 wbar ≤ Chat * norm2 h := by sorry

end WrightPDIPM.Termination
