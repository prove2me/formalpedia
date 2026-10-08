-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_theorem_5_3
-- name    : ZhangBSDE.Scheme.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:04:03.986629+00:00
-- url     : https://prove2.me/theorems/f062bcef-5285-4f61-bee4-2c3f98ddac57
-- title:
--   Theorem 5.3, p. 479 — max_i E|Y_{t_i} − Y^π_{t_i}|² + E∫|Z_r − Z^π_r|²dr ≤ C[(1+|x|²)|π| + E|ξ − ξ^π|²] for K-uniform π
-- statement:
--   Assume Assumption 2.3 with constant $K$, let $(X,Y,Z)$ solve (2.1) started at $x$ with $Z$ càdlàg, and put $\xi=\Phi(X)$. Let $\kappa>0$. There is a constant $C>0$, depending only on $T$, $K$ and $\kappa$ (and $d$), such that for every $\kappa$-uniform partition $\pi$, every $\xi^\pi\in L^2(\mathcal F_T)$ and every solution $(Y^\pi,Z^\pi)$ of the backward scheme (5.1)–(5.2) with terminal value $\xi^\pi$,
--   $$\max_{0\le i\le n}E\{|Y_{t_i}-Y^\pi_{t_i}|^2\}+E\Big\{\int_0^T|Z_r-Z^\pi_r|^2dr\Big\}\le C\big[(1+|x|^2)|\pi|+E\{|\xi-\xi^\pi|^2\}\big].$$
--
--   This is the convergence of the backward scheme at the grid points; with Theorem 3.1 it gives the step-process estimate of Theorem 5.6.
--
--   **Formalization Note** The paper calls the uniformity constant $K$ (the letter of the Lipschitz constant) and says "$C$ depends only on $T$ and $K$"; here the uniformity constant is $\kappa$ and $C$ may depend on it. The maximum over $i$ is stated as a bound for each $i\le n$. No smallness of $|\pi|$ is assumed, as on the page (the proof works for $|\pi|$ small; coarse uniform partitions have boundedly many steps). Expectations are lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Theorem 5.3, p. 479 (proof pp. 480–482)

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_BackwardScheme

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Theorem 5.3 (p. 479): under the conditions of Theorem 3.1 (Assumption 2.3, `Z` càdlàg), there is
`C > 0`, depending only on `T`, `K` and the uniformity constant `κ` (and `d`), such that for every
`κ`-uniform partition `π`, every terminal value `ξ^π ∈ L²(𝓕_T)` and every solution `(Y^π, Z^π)` of the
scheme (5.1)–(5.2), with `ξ = Φ(X)`,
`max_{0≤i≤n} E{|Y_{t_i} − Y^π_{t_i}|²} + E{∫₀ᵀ |Z_r − Z^π_r|² dr} ≤ C[(1 + |x|²)|π| + E{|ξ − ξ^π|²}]`
(stated for each `i`). -/
theorem theorem_5_3 {d : ℕ} (T : ℝ≥0) (K κ : ℝ) (hT : 0 < T) (hK : 0 < K) (hκ : 0 < κ) :
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
        ∀ i ≤ π.n,
          ∫⁻ ω, ‖Y (π.tt i) ω - Yπ (π.tt i) ω‖ₑ ^ 2 ∂P
              + ∫⁻ ω, ∫⁻ r in Icc (0 : ℝ) T, ‖Z r.toNNReal ω - Zπ r.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
            ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh)
              + ENNReal.ofReal C * ∫⁻ ω, ‖Φ (fun t => X t ω) - ξπ ω‖ₑ ^ 2 ∂P := by sorry

end ZhangBSDE.Scheme
