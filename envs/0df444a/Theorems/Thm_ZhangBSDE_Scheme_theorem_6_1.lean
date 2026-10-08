-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_theorem_6_1
-- name    : ZhangBSDE.Scheme.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:04:01.742924+00:00
-- url     : https://prove2.me/theorems/2c52cb20-5a07-4589-9d3e-36e78713aa07
-- title:
--   Theorem 6.1, (6.5)–(6.6), p. 484 — sup_t E|Y_t − Ŷ^π_t|² + E∫|Z_t − Ẑ^π_t|²dt ≤ C(1+|x|²)|π|log(1/|π|), and ≤ C(1+|x|²)|π| for L¹-Lipschitz or Markovian Φ
-- statement:
--   Let $W$ be a one-dimensional Brownian motion with its augmented natural filtration, assume Assumption 2.3 with constant $K$, let $(X,Y,Z)$ solve the forward–backward SDE (2.1) started at $x\in\mathbb R^d$, and assume $Z$ is càdlàg. For a partition $\pi$, let $\hat X^\pi$ be the step process of the Euler scheme, put $\xi^\pi=\Phi(\hat X^\pi)$, let $(Y^\pi,Z^\pi)$ solve the backward scheme (5.1)–(5.2) with terminal value $\xi^\pi$, and let $\hat Y^\pi,\hat Z^\pi$ be its step processes. Write
--   $$\mathcal E(\pi)=\sup_{0\le t\le T}E\{|Y_t-\hat Y^\pi_t|^2\}+E\Big\{\int_0^T|Z_t-\hat Z^\pi_t|^2dt\Big\}.$$
--   Let $\kappa>0$. There is a constant $C>0$, depending only on $T$, $K$ and $\kappa$ (and $d$), such that for every partition $\pi$ for which $f$ is independent of $z$ or $\pi$ is $\kappa$-uniform:
--
--   1. (6.5) if $|\pi|\le e^{-1/2}$, then $\mathcal E(\pi)\le C(1+|x|^2)|\pi|\log\frac1{|\pi|}$;
--   2. (6.6) if $\Phi$ is $L^1$-Lipschitz (2.3) or has the form $\Phi(X)=g(X_T)$, then $\mathcal E(\pi)\le C(1+|x|^2)|\pi|$.
--
--   This is the paper's convergence theorem for its fully implementable scheme: the step-process approximations converge in mean square at rate $|\pi|\log(1/|\pi|)$ for path-dependent $L^\infty$-Lipschitz terminal values, and at rate $|\pi|$ for $L^1$-Lipschitz or Markovian ones.
--
--   **Formalization Note** The paper's uniformity constant is named $K$; here it is $\kappa$, and $C$ may depend on it (in the "$f$ independent of $z$" case one may take $\kappa=1$, so $C$ depends on $T$ and $K$ only). The restriction $|\pi|\le e^{-1/2}$ in (6.5) is the paper's "$\pi$ fine enough" from the proof of Theorem 4.2 (p. 478); for $|\pi|\ge1$ the bound would be false. "$Z$ is càdlàg" includes $Z_T=Z_{T-}$. The step processes take the values $\hat X^\pi_T=X^\pi_T$, $\hat Y^\pi_T=Y^\pi_T$, $\hat Z^\pi_T=0$. "Moreover" in (6.6) continues the sentence of (6.5), so (6.6) keeps the hypothesis "$f$ independent of $z$ or $\pi$ uniform". Expectations are lower Lebesgue integrals in $[0,\infty]$, so a non-integrable error cannot make the bound vacuous. The scheme is constructed from the data; only the solutions $(X,Y,Z)$ and $(Y^\pi,Z^\pi)$ are quantified. The representation (6.3)–(6.4) of the same theorem is not part of this statement.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Theorem 6.1 (6.5)–(6.6), p. 484; scheme (5.1)–(5.2), p. 479; step processes p. 482; ξ^π = Φ(X̂^π), p. 483

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_BackwardScheme

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Theorem 6.1, (6.5)–(6.6) (p. 484): under the conditions of Theorem 3.1, there is `C > 0`,
depending only on `T`, `K` and `κ` (and `d`), such that for every partition `π` for which `f` is
independent of `z` or `π` is `κ`-uniform, and every solution `(Y^π, Z^π)` of the scheme
(5.1)–(5.2) with terminal value `ξ^π = Φ(X̂^π)`, writing
`err = sup_{0≤t≤T} E{|Y_t − Ŷ^π_t|²} + E{∫₀ᵀ |Z_t − Ẑ^π_t|² dt}`:
(6.5) if `|π| ≤ e^{−1/2}`, `err ≤ C (1 + |x|²) |π| log(1/|π|)`;
(6.6) if `Φ` is `L¹`-Lipschitz or `Φ(X) = g(X_T)`, `err ≤ C (1 + |x|²) |π|`. -/
theorem theorem_6_1 {d : ℕ} (T : ℝ≥0) (K κ : ℝ) (hT : 0 < T) (hK : 0 < K) (hκ : 0 < κ) :
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
        ∀ π : Partition T, (IndepZ f ∨ π.IsUniform κ) →
        ∀ Yπ Zπ : ℝ≥0 → Ω → ℝ,
        IsBackwardScheme (augmentedFiltration P hB) P T (fun t ω => B t ω 0) π x b σ f
          (fun ω => Φ (fun t => stepX π x b σ (fun t ω => B t ω 0) t ω)) Yπ Zπ →
        (π.mesh ≤ Real.exp (-1 / 2) →
          (⨆ t ∈ Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖Y t ω - Yhat π Yπ t ω‖ₑ ^ 2 ∂P)
              + ∫⁻ ω, ∫⁻ r in Icc (0 : ℝ) T,
                  ‖Z r.toNNReal ω - Zhat (augmentedFiltration P hB) P π Zπ r.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
            ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh * Real.log (1 / π.mesh))) ∧
        (IsL1Lipschitz T K Φ ∨ IsMarkovian T Φ →
          (⨆ t ∈ Icc (0 : ℝ≥0) T, ∫⁻ ω, ‖Y t ω - Yhat π Yπ t ω‖ₑ ^ 2 ∂P)
              + ∫⁻ ω, ∫⁻ r in Icc (0 : ℝ) T,
                  ‖Z r.toNNReal ω - Zhat (augmentedFiltration P hB) P π Zπ r.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
            ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh)) := by sorry

end ZhangBSDE.Scheme
