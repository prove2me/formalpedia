-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_theorem_5_6
-- name    : ZhangBSDE.Scheme.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:45.103766+00:00
-- url     : https://prove2.me/theorems/737d6204-7d5e-4408-b9ed-37624b3183ec
-- title:
--   Theorem 5.6, pp. 482–483 — sup_t E|Y_t − Ŷ^π_t|² + E∫|Z_r − Ẑ^π_r|²dr ≤ C[(1+|x|²)|π| + E|ξ − ξ^π|²] for K-uniform π
-- statement:
--   Assume Assumption 2.3 with constant $K$, let $(X,Y,Z)$ solve (2.1) started at $x$ with $Z$ càdlàg, and put $\xi=\Phi(X)$. Let $\kappa>0$. There is a constant $C>0$, depending only on $T$, $K$ and $\kappa$ (and $d$), such that for every $\kappa$-uniform partition $\pi$, every $\xi^\pi\in L^2(\mathcal F_T)$ and every solution $(Y^\pi,Z^\pi)$ of (5.1)–(5.2) with terminal value $\xi^\pi$, the step processes $\hat Y^\pi,\hat Z^\pi$ satisfy
--   $$\sup_{0\le t\le T}E\{|Y_t-\hat Y^\pi_t|^2\}+E\Big\{\int_0^T|Z_r-\hat Z^\pi_r|^2dr\Big\}\le C\big[(1+|x|^2)|\pi|+E\{|\xi-\xi^\pi|^2\}\big].$$
--
--   Combined with Corollary 4.4 for $\xi^\pi=\Phi(\hat X^\pi)$, this gives Theorem 6.1.
--
--   **Formalization Note** Uniformity constant $\kappa$ as in Theorem 5.3. The supremum includes $t=T$, where $\hat Y^\pi_T=Y^\pi_T=\xi^\pi$; the step process $\hat Z^\pi$ is $0$ at $T$.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Theorem 5.6, pp. 482–483

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_BackwardScheme

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Theorem 5.6 (pp. 482–483): under the conditions of Theorem 3.1, there is `C > 0`, depending only
on `T`, `K` and the uniformity constant `κ` (and `d`), such that for every `κ`-uniform partition `π`,
every `ξ^π ∈ L²(𝓕_T)` and every solution `(Y^π, Z^π)` of (5.1)–(5.2), with the step processes
`Ŷ^π, Ẑ^π` and `ξ = Φ(X)`,
`sup_{0≤t≤T} E{|Y_t − Ŷ^π_t|²} + E{∫₀ᵀ |Z_r − Ẑ^π_r|² dr} ≤ C[(1 + |x|²)|π| + E{|ξ − ξ^π|²}]`. -/
theorem theorem_5_6 {d : ℕ} (T : ℝ≥0) (K κ : ℝ) (hT : 0 < T) (hK : 0 < K) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (x : EuclideanSpace ℝ (Fin d)) (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ)
        (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ),
        Assumption23 T K b σ f Φ →
        ∀ (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (Y Z : ℝ≥0 → Ω → ℝ),
        IsFBSDESolution (augmentedFiltration P hB) P T (fun t ω => B t ω 0) x b σ f Φ X Y Z →
        ZCadlag P T Z →
        ∀ π : Partition T, π.IsUniform κ →
        ∀ (ξπ : Ω → ℝ), IsTerminalValue (augmentedFiltration P hB) P T ξπ →
        ∀ Yπ Zπ : ℝ≥0 → Ω → ℝ,
        IsBackwardScheme (augmentedFiltration P hB) P T (fun t ω => B t ω 0) π x b σ f ξπ Yπ Zπ →
          (⨆ t ∈ Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖Y t ω - Yhat π Yπ t ω‖ₑ ^ 2 ∂P)
              + ∫⁻ ω, ∫⁻ r in Icc (0 : ℝ) T,
                  ‖Z r.toNNReal ω - Zhat (augmentedFiltration P hB) P π Zπ r.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
            ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh)
              + ENNReal.ofReal C * ∫⁻ ω, ‖Φ (fun t => X t ω) - ξπ ω‖ₑ ^ 2 ∂P := by sorry

end ZhangBSDE.Scheme
