-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_theorem_3_1
-- name    : ZhangBSDE.Scheme.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:15.820463+00:00
-- url     : https://prove2.me/theorems/b505da19-bec9-4c00-8274-c74e66d5b1e0
-- title:
--   Theorem 3.1, p. 465 — L²-regularity of Z: Σ_i E∫_{t_{i−1}}^{t_i} [|Z_t − Z_{t_{i−1}}|² + |Z_t − Z_{t_i}|²] dt ≤ C(1+|x|²)|π|
-- statement:
--   Assume Assumption 2.3 with constant $K$, let $(X,Y,Z)$ solve the forward–backward SDE (2.1) started at $x$, and assume $Z$ is càdlàg. There is a constant $C>0$, depending only on $T$ and $K$ (and $d$) and independent of the partition, such that for every partition $\pi:0=t_0<\dots<t_n=T$,
--   $$\sum_{i=1}^n E\Big\{\int_{t_{i-1}}^{t_i}\big[|Z_t-Z_{t_{i-1}}|^2+|Z_t-Z_{t_i}|^2\big]dt\Big\}\le C(1+|x|^2)|\pi| .$$
--
--   This is the paper's first main result, the $L^2$-regularity of the martingale integrand; it is what makes the rate $|\pi|$ possible in the analysis of the backward scheme (Theorems 5.3 and 5.6).
--
--   **Formalization Note** "$Z$ is càdlàg" includes $Z_T=Z_{T-}$ almost surely: $Z$ is determined only $dt\otimes dP$-a.e., and the $i=n$ term evaluates $Z$ at $t_n=T$, so without this pin the statement would fail (change $Z_T$). $C$ is chosen before the probability space, the data, the solution and the partition; it may depend on $d$, which the paper fixes.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Theorem 3.1, p. 465 (proof pp. 469–476)

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_FBSDE

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Theorem 3.1 (p. 465), the `L²`-regularity of `Z`: under Assumption 2.3, if `Z` is càdlàg, there
is `C > 0`, depending only on `T` and `K` (and `d`), such that for every partition `π`,
`Σ_{i=1}^n E{∫_{t_{i−1}}^{t_i} [|Z_t − Z_{t_{i−1}}|² + |Z_t − Z_{t_i}|²] dt} ≤ C (1 + |x|²) |π|`. -/
theorem theorem_3_1 {d : ℕ} (T : ℝ≥0) (K : ℝ) (hT : 0 < T) (hK : 0 < K) :
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
        ∀ π : Partition T,
          ∑ i ∈ Finset.Icc 1 π.n, ∫⁻ ω, ∫⁻ t in Icc (π.tt (i - 1) : ℝ) (π.tt i),
              (‖Z t.toNNReal ω - Z (π.tt (i - 1)) ω‖ₑ ^ 2 + ‖Z t.toNNReal ω - Z (π.tt i) ω‖ₑ ^ 2) ∂volume ∂P
            ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh) := by sorry

end ZhangBSDE.Scheme
