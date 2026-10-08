-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_lemma_3_3
-- name    : ZhangBSDE.Scheme.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:20.108989+00:00
-- url     : https://prove2.me/theorems/f006fad0-65eb-4d42-8df0-fbf4103b787f
-- title:
--   Lemma 3.3, p. 467 — E{Σ_i ∫_{t_{i−1}}^{t_{i+1}} |Σ_{j≥i} η^j_r|² dr Λ_{t_{i−1}}} ≤ C E{(sup_t Σ_j |ξ^j_t|)² Λ*_T}
-- statement:
--   Let $W$ be a one-dimensional Brownian motion with its augmented natural filtration $\mathbb F$, and let $\pi:0=t_0<\dots<t_n=T$ be a partition, with $t_{n+1}=t_n$. Let $\Lambda\in L^2(\mathbb F)$ and $\eta^j\in L^2(\mathbb F)$, $j=1,\dots,n$, let $\alpha_j$ be constants, and put $\xi^j_t=\alpha_j+\int_0^t\eta^j_r\,dW_r$ and $\Lambda^*_T=\sup_{0\le s\le T}|\Lambda_s|$. There is a constant $C>0$, independent of everything, such that
--   $$E\Big\{\sum_{i=1}^n\int_{t_{i-1}}^{t_{i+1}}\Big|\sum_{j\ge i}\eta^j_r\Big|^2dr\;|\Lambda_{t_{i-1}}|\Big\}\le C\,E\Big\{\Big(\sup_{0\le t\le T}\sum_{j=1}^n|\xi^j_t|\Big)^2\Lambda^*_T\Big\}.$$
--
--   This is the building block of the proof of the $L^2$-regularity theorem (Theorem 3.1).
--
--   **Formalization Note** The page writes the signed $\Lambda_{t_{i-1}}$ on the left; its proof first bounds it by $\Lambda^*_{t_{i-1}}\ge|\Lambda_{t_{i-1}}|$. The statement uses $|\Lambda_{t_{i-1}}|$, which implies the page's inequality and keeps both sides in $[0,\infty]$. The constant $C$ is absolute: it is chosen before the probability space, $T$ and the partition. The stochastic integrals are $L^2$ Itô integrals; the statement holds for every version $J^j$ of $\int_0^\cdot\eta^j\,dW$, which is at least as strong as the statement for the continuous version.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Lemma 3.3, p. 467

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_Setting

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Lemma 3.3 (p. 467): there is an absolute constant `C > 0` such that for every partition `π` of
`[0, T]`, every `Λ ∈ L²(𝔽)`, every `η^j ∈ L²(𝔽)` (`j = 1, …, n`) and all constants `α_j`, with
`ξ^j_t = α_j + ∫₀ᵗ η^j_r dW_r`,
`E{Σ_{i=1}^n ∫_{t_{i−1}}^{t_{i+1}} |Σ_{j≥i} η^j_r|² dr |Λ_{t_{i−1}}|} ≤ C E{(sup_{0≤t≤T} Σ_{j=1}^n |ξ^j_t|)² Λ*_T}`,
where `t_{n+1} = t_n` and `Λ*_T = sup_{0≤s≤T} |Λ_s|`. -/
theorem lemma_3_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (T : ℝ≥0) (π : Partition T) (Λ : ℝ≥0 → Ω → ℝ)
        (η : ℕ → ℝ≥0 → Ω → ℝ) (α : ℕ → ℝ) (J : ℕ → ℝ≥0 → Ω → ℝ),
        L2F (augmentedFiltration P hB) P T Λ →
        (∀ j ∈ Finset.Icc 1 π.n, IsItoIntegral (augmentedFiltration P hB) P T (fun t ω => B t ω 0) (η j) (J j)) →
        ∑ i ∈ Finset.Icc 1 π.n, ∫⁻ ω,
            (∫⁻ r in Icc (π.tt (i - 1) : ℝ) (π.tt (i + 1)),
              ‖∑ j ∈ Finset.Icc i π.n, η j r.toNNReal ω‖ₑ ^ 2) * ‖Λ (π.tt (i - 1)) ω‖ₑ ∂P
          ≤ ENNReal.ofReal C * ∫⁻ ω,
              (⨆ t ∈ Icc (0 : ℝ≥0) T, ∑ j ∈ Finset.Icc 1 π.n, ‖α j + J j t ω‖ₑ) ^ 2
                * (⨆ s ∈ Icc (0 : ℝ≥0) T, ‖Λ s ω‖ₑ) ∂P := by sorry

end ZhangBSDE.Scheme
