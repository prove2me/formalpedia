-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_theorem_4_2
-- name    : ZhangBSDE.Scheme.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:39.017429+00:00
-- url     : https://prove2.me/theorems/69acff73-1a7e-4ebe-a3af-31b13870275a
-- title:
--   Theorem 4.2, p. 477 — sup_t E|X_t − X̂^π_t|² ≤ C(1+|x|²)|π| and E sup_t |X_t − X̂^π_t|² ≤ C(1+|x|²)|π| log(1/|π|)
-- statement:
--   Assume $b$ and $\sigma$ satisfy the conditions of Assumption 2.3 with constant $K$, let $X$ solve the forward SDE in (2.1) started at $x$, and let $\hat X^\pi$ be the step process (4.2) of the Euler scheme. There is a constant $C>0$, depending only on $T$ and $K$ (and $d$), such that for every partition $\pi$
--   $$\sup_{0\le t\le T}E\{|X_t-\hat X^\pi_t|^2\}\le C(1+|x|^2)|\pi| ,$$
--   and, for every partition with $|\pi|\le e^{-1/2}$,
--   $$E\Big\{\sup_{0\le t\le T}|X_t-\hat X^\pi_t|^2\Big\}\le C(1+|x|^2)|\pi|\log\frac1{|\pi|}.$$
--
--   The logarithmic factor in the uniform estimate is sharp (Remark 4.3); it is the source of the rate $|\pi|\log(1/|\pi|)$ in Theorem 6.1.
--
--   **Formalization Note** The restriction $|\pi|\le e^{-1/2}$ is the paper's "assuming that the partition $\pi$ is fine enough so that $a\ge1$", $a=2\log(1/|\pi|)$ (p. 478); for $|\pi|\ge1$ the right-hand side is $\le0$ and the estimate would be false. $\hat X^\pi_T=X^\pi_T$.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Theorem 4.2, p. 477 (proof pp. 477–478)

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_FBSDE
import Definitions.Def_ZhangBSDE_Scheme_Euler

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Theorem 4.2 (p. 477): if `b` and `σ` satisfy the conditions of Assumption 2.3, there is `C > 0`,
depending only on `T` and `K` (and `d`), such that for every partition `π`,
`sup_{0≤t≤T} E{|X_t − X̂^π_t|²} ≤ C (1 + |x|²) |π|`, and, when `|π| ≤ e^{−1/2}`,
`E{sup_{0≤t≤T} |X_t − X̂^π_t|²} ≤ C (1 + |x|²) |π| log(1/|π|)`. -/
theorem theorem_4_2 {d : ℕ} (T : ℝ≥0) (K : ℝ) (hT : 0 < T) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (x : EuclideanSpace ℝ (Fin d)) (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
        ForwardCoeff T K b σ →
        ∀ X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
        IsForwardSolution (augmentedFiltration P hB) P T (fun t ω => B t ω 0) x b σ X →
        ∀ π : Partition T,
          (⨆ t ∈ Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖X t ω - stepX π x b σ (fun t ω => B t ω 0) t ω‖ₑ ^ 2 ∂P)
              ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh) ∧
            (π.mesh ≤ Real.exp (-1 / 2) →
              ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ≥0) T, ‖X t ω - stepX π x b σ (fun t ω => B t ω 0) t ω‖ₑ ^ 2 ∂P
                ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh * Real.log (1 / π.mesh))) := by sorry

end ZhangBSDE.Scheme
