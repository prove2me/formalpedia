-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_remark_5_5
-- name    : ZhangBSDE.Scheme.remark_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:41.6903+00:00
-- url     : https://prove2.me/theorems/b9be8777-71b8-428e-89f7-c8a6d3234375
-- title:
--   Remark 5.5, p. 482 — if f is independent of z, Theorem 5.3 holds without the K-uniform assumption
-- statement:
--   Assume Assumption 2.3 with constant $K$, let $(X,Y,Z)$ solve (2.1) started at $x$ with $Z$ càdlàg, put $\xi=\Phi(X)$, and assume the driver $f$ does not depend on $z$. There is a constant $C>0$, depending only on $T$ and $K$ (and $d$), such that for **every** partition $\pi$, every $\xi^\pi\in L^2(\mathcal F_T)$ and every solution $(Y^\pi,Z^\pi)$ of the backward scheme (5.1)–(5.2) with terminal value $\xi^\pi$,
--   $$\max_{0\le i\le n}E\{|Y_{t_i}-Y^\pi_{t_i}|^2\}+E\Big\{\int_0^T|Z_r-Z^\pi_r|^2dr\Big\}\le C\big[(1+|x|^2)|\pi|+E\{|\xi-\xi^\pi|^2\}\big].$$
--
--   It is the input for the "$f$ independent of $z$" branch of Theorem 6.1.
--
--   **Formalization Note** The remark states that the uniformity assumption of Theorem 5.3 "is not necessary" when $f$ is independent of $z$; this item states that claim as a theorem, with $C$ depending on $T$ and $K$ only.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Remark 5.5, p. 482

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_BackwardScheme

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Remark 5.5 (p. 482): if `f` is independent of `z`, the conclusion of Theorem 5.3 holds for every
partition `π` (no uniformity assumption), with `C > 0` depending only on `T` and `K` (and `d`). -/
theorem remark_5_5 {d : ℕ} (T : ℝ≥0) (K : ℝ) (hT : 0 < T) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (x : EuclideanSpace ℝ (Fin d)) (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ)
        (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ),
        Assumption23 T K b σ f Φ →
        ∀ (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (Y Z : ℝ≥0 → Ω → ℝ),
        IsFBSDESolution (augmentedFiltration P hB) P T (fun t ω => B t ω 0) x b σ f Φ X Y Z →
        ZCadlag P T Z → IndepZ f →
        ∀ π : Partition T,
        ∀ (ξπ : Ω → ℝ), IsTerminalValue (augmentedFiltration P hB) P T ξπ →
        ∀ Yπ Zπ : ℝ≥0 → Ω → ℝ,
        IsBackwardScheme (augmentedFiltration P hB) P T (fun t ω => B t ω 0) π x b σ f ξπ Yπ Zπ →
        ∀ i ≤ π.n,
          ∫⁻ ω, ‖Y (π.tt i) ω - Yπ (π.tt i) ω‖ₑ ^ 2 ∂P
              + ∫⁻ ω, ∫⁻ r in Icc (0 : ℝ) T, ‖Z r.toNNReal ω - Zπ r.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
            ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh)
              + ENNReal.ofReal C * ∫⁻ ω, ‖Φ (fun t => X t ω) - ξπ ω‖ₑ ^ 2 ∂P := by sorry

end ZhangBSDE.Scheme
