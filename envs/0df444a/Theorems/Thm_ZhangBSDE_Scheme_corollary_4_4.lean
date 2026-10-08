-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_corollary_4_4
-- name    : ZhangBSDE.Scheme.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:01.634995+00:00
-- url     : https://prove2.me/theorems/7e6a3278-061c-4279-8093-7a9ca3f4a661
-- title:
--   Corollary 4.4, p. 478 — E|Φ(X) − Φ(X̂^π)|² ≤ C(1+|x|²)|π| log(1/|π|), and ≤ C(1+|x|²)|π| for L¹-Lipschitz or Markovian Φ
-- statement:
--   Assume $b,\sigma$ satisfy the conditions of Assumption 2.3 with constant $K$ and $\Phi$ is $L^\infty$-Lipschitz (2.2) with constant $K$. Let $X$ solve the forward SDE in (2.1) started at $x$ and let $\hat X^\pi$ be the Euler step process. There is a constant $C>0$, depending only on $T$ and $K$ (and $d$), such that for every partition $\pi$ with $|\pi|\le e^{-1/2}$
--   $$E\{|\Phi(X)-\Phi(\hat X^\pi)|^2\}\le C(1+|x|^2)|\pi|\log\frac1{|\pi|},$$
--   and, if moreover $\Phi$ is $L^1$-Lipschitz (2.3) with constant $K$ or has the form $\Phi(X)=g(X_T)$, then for every partition $\pi$
--   $$E\{|\Phi(X)-\Phi(\hat X^\pi)|^2\}\le C(1+|x|^2)|\pi| .$$
--
--   This controls the terminal-value error $E|\xi-\xi^\pi|^2$ of the backward scheme with $\xi^\pi=\Phi(\hat X^\pi)$.
--
--   **Formalization Note** $|\pi|\le e^{-1/2}$ as in Theorem 4.2. The Lipschitz constants of (2.2) and (2.3) are taken to be the common $K$ of Assumption 2.3. In the Markovian case $g$ is $K$-Lipschitz because $\Phi$ is $L^\infty$-Lipschitz.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Corollary 4.4, p. 478

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_FBSDE
import Definitions.Def_ZhangBSDE_Scheme_Euler

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Corollary 4.4 (p. 478): under the conditions of Theorem 4.2, if `Φ` is `L^∞`-Lipschitz (2.2) with
constant `K`, there is `C > 0`, depending only on `T` and `K` (and `d`), such that for every
partition `π` with `|π| ≤ e^{−1/2}`, `E{|Φ(X) − Φ(X̂^π)|²} ≤ C (1 + |x|²) |π| log(1/|π|)`; and if
moreover `Φ` is `L¹`-Lipschitz (2.3) or of the form `Φ(X) = g(X_T)`, then for every partition `π`,
`E{|Φ(X) − Φ(X̂^π)|²} ≤ C (1 + |x|²) |π|`. -/
theorem corollary_4_4 {d : ℕ} (T : ℝ≥0) (K : ℝ) (hT : 0 < T) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (x : EuclideanSpace ℝ (Fin d)) (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ) (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
        ForwardCoeff T K b σ → IsLinfLipschitz T K Φ →
        ∀ X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
        IsForwardSolution (augmentedFiltration P hB) P T (fun t ω => B t ω 0) x b σ X →
        ∀ π : Partition T,
          (π.mesh ≤ Real.exp (-1 / 2) →
            ∫⁻ ω, ‖Φ (fun t => X t ω) - Φ (fun t => stepX π x b σ (fun t ω => B t ω 0) t ω)‖ₑ ^ 2 ∂P
              ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh * Real.log (1 / π.mesh))) ∧
          (IsL1Lipschitz T K Φ ∨ IsMarkovian T Φ →
            ∫⁻ ω, ‖Φ (fun t => X t ω) - Φ (fun t => stepX π x b σ (fun t ω => B t ω 0) t ω)‖ₑ ^ 2 ∂P
              ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh)) := by sorry

end ZhangBSDE.Scheme
