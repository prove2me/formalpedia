-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_lemma_4_1
-- name    : ZhangBSDE.Scheme.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:55.333988+00:00
-- url     : https://prove2.me/theorems/183a5afb-604b-4943-83f1-75d11b4738af
-- title:
--   Lemma 4.1, p. 476 — E sup_t |X^π_t|⁴ ≤ C(1+|x|⁴) and E sup_t |X_t − X^π_t|² ≤ C(1+|x|²)|π|
-- statement:
--   Assume $b$ and $\sigma$ satisfy the conditions of Assumption 2.3 with constant $K$. Let $X$ solve the forward SDE in (2.1) started at $x$, and let $X^\pi$ be the Euler process (4.1) of a partition $\pi$. There is a constant $C>0$, depending only on $T$ and $K$ (and $d$), such that for every partition $\pi$
--   $$E\Big\{\sup_{0\le t\le T}|X^\pi_t|^4\Big\}\le C(1+|x|^4),\qquad E\Big\{\sup_{0\le t\le T}|X_t-X^\pi_t|^2\Big\}\le C(1+|x|^2)|\pi| .$$
--
--   These are the standard moment and strong-error estimates of the Euler scheme, used in Theorem 4.2.
--
--   **Formalization Note** The page says "defined as in (1.1)"; equation (2.1) is meant. Only the $b,\sigma$ part of Assumption 2.3 is assumed. The page writes "a constant $C$"; a positive one is required here, which is equivalent.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Lemma 4.1, p. 476

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_FBSDE
import Definitions.Def_ZhangBSDE_Scheme_Euler

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Lemma 4.1 (p. 476): if `b` and `σ` satisfy the conditions of Assumption 2.3, there is `C > 0`,
depending only on `T` and `K` (and `d`), such that for the solution `X` of the forward SDE in (2.1)
and the Euler process `X^π` of (4.1), for every partition `π`,
`E{sup_{0≤t≤T} |X^π_t|⁴} ≤ C (1 + |x|⁴)` and `E{sup_{0≤t≤T} |X_t − X^π_t|²} ≤ C (1 + |x|²) |π|`. -/
theorem lemma_4_1 {d : ℕ} (T : ℝ≥0) (K : ℝ) (hT : 0 < T) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (x : EuclideanSpace ℝ (Fin d)) (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
        ForwardCoeff T K b σ →
        ∀ X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
        IsForwardSolution (augmentedFiltration P hB) P T (fun t ω => B t ω 0) x b σ X →
        ∀ π : Partition T,
          ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ≥0) T, ‖euler π x b σ (fun t ω => B t ω 0) t ω‖ₑ ^ 4 ∂P
              ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 4)) ∧
            ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ≥0) T, ‖X t ω - euler π x b σ (fun t ω => B t ω 0) t ω‖ₑ ^ 2 ∂P
              ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh) := by sorry

end ZhangBSDE.Scheme
