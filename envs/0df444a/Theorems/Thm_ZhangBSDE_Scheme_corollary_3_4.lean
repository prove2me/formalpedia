-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_corollary_3_4
-- name    : ZhangBSDE.Scheme.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:06.089704+00:00
-- url     : https://prove2.me/theorems/92f89e7e-46e2-4715-b654-d0c4d3cb8668
-- title:
--   Corollary 3.4, p. 469 — E{Σ_i ∫_{t_{i−1}}^{t_{i+1}} |η_r|² dr Λ_{t_{i−1}}} ≤ C E{sup_t |ξ_t|² Λ*_T}
-- statement:
--   In the setting of Lemma 3.3 (a one-dimensional Brownian motion $W$ with its augmented filtration, a partition $\pi$ with $t_{n+1}=t_n$), let $\eta,\Lambda\in L^2(\mathbb F)$, let $\alpha$ be a constant and $\xi_t=\alpha+\int_0^t\eta_r\,dW_r$. There is an absolute constant $C>0$ such that
--   $$E\Big\{\sum_{i=1}^n\int_{t_{i-1}}^{t_{i+1}}|\eta_r|^2dr\;|\Lambda_{t_{i-1}}|\Big\}\le C\,E\Big\{\sup_{0\le t\le T}|\xi_t|^2\,\Lambda^*_T\Big\},\qquad \Lambda^*_T=\sup_{0\le s\le T}|\Lambda_s| .$$
--
--   It is the one-integrand case of Lemma 3.3 ($\xi^n=\xi$, $\xi^j=0$ for $j<n$) and is the form used in the proof of Theorem 3.1.
--
--   **Formalization Note** As in Lemma 3.3, $|\Lambda_{t_{i-1}}|$ replaces the page's signed $\Lambda_{t_{i-1}}$, which only strengthens the statement.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Corollary 3.4, p. 469

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_Setting

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Corollary 3.4 (p. 469): with the absolute constant `C` of Lemma 3.3, if
`ξ_t = α + ∫₀ᵗ η_r dW_r` and `η, Λ ∈ L²(𝔽)`, then
`E{Σ_{i=1}^n ∫_{t_{i−1}}^{t_{i+1}} |η_r|² dr |Λ_{t_{i−1}}|} ≤ C E{sup_{0≤t≤T} |ξ_t|² Λ*_T}`. -/
theorem corollary_3_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (T : ℝ≥0) (π : Partition T) (Λ η : ℝ≥0 → Ω → ℝ) (α : ℝ) (J : ℝ≥0 → Ω → ℝ),
        L2F (augmentedFiltration P hB) P T Λ →
        IsItoIntegral (augmentedFiltration P hB) P T (fun t ω => B t ω 0) η J →
        ∑ i ∈ Finset.Icc 1 π.n, ∫⁻ ω,
            (∫⁻ r in Icc (π.tt (i - 1) : ℝ) (π.tt (i + 1)), ‖η r.toNNReal ω‖ₑ ^ 2)
              * ‖Λ (π.tt (i - 1)) ω‖ₑ ∂P
          ≤ ENNReal.ofReal C * ∫⁻ ω,
              (⨆ t ∈ Icc (0 : ℝ≥0) T, ‖α + J t ω‖ₑ ^ 2) * (⨆ s ∈ Icc (0 : ℝ≥0) T, ‖Λ s ω‖ₑ) ∂P := by sorry

end ZhangBSDE.Scheme
