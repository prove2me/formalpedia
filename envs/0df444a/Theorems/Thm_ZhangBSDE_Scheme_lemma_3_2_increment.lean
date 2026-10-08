-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_lemma_3_2_increment
-- name    : ZhangBSDE.Scheme.lemma_3_2_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:57.016978+00:00
-- url     : https://prove2.me/theorems/74bd4abd-4b09-4654-8094-2c4920d71b65
-- title:
--   Lemma 3.2 (3.2), pp. 465–466 — E{|X_t − X_{t_{i−1}}|² + |Y_t − Y_{t_{i−1}}|²} ≤ C(1+|x|²)|π|
-- statement:
--   Assume Assumption 2.3 with constant $K$, and let $(X,Y,Z)$ solve (2.1) started at $x$. There is a constant $C>0$, depending only on $T$ and $K$ (and $d$) and independent of the partition, such that for every partition $\pi:0=t_0<\dots<t_n=T$,
--   $$\max_{1\le i\le n}\ \sup_{t\in(t_{i-1},t_i]}E\big\{|X_t-X_{t_{i-1}}|^2+|Y_t-Y_{t_{i-1}}|^2\big\}\le C(1+|x|^2)|\pi| .$$
--
--   This is the time-regularity of the forward and backward components; it enters the proofs of Theorems 4.2 and 5.6.
--
--   **Formalization Note** The max/sup is written as "for every $i$ and every $t\in(t_{i-1},t_i]$"; the expectation is a lower Lebesgue integral in $[0,\infty]$, so it cannot vanish by non-integrability. $C$ is chosen before the probability space, the data, the solution and the partition.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Lemma 3.2 (3.2), pp. 465–466

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_FBSDE

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Lemma 3.2, (3.2) (pp. 465–466): under Assumption 2.3 there is `C > 0`, depending only on `T`
and `K` (and `d`), such that for every partition `π`, every `i = 1, …, n` and every
`t ∈ (t_{i−1}, t_i]`, `E{|X_t − X_{t_{i−1}}|² + |Y_t − Y_{t_{i−1}}|²} ≤ C (1 + |x|²) |π|`. -/
theorem lemma_3_2_increment {d : ℕ} (T : ℝ≥0) (K : ℝ) (hT : 0 < T) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (x : EuclideanSpace ℝ (Fin d)) (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ)
        (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ),
        Assumption23 T K b σ f Φ →
        ∀ (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (Y Z : ℝ≥0 → Ω → ℝ),
        IsFBSDESolution (augmentedFiltration P hB) P T (fun t ω => B t ω 0) x b σ f Φ X Y Z →
        ∀ π : Partition T, ∀ i ∈ Finset.Icc 1 π.n, ∀ t : ℝ≥0, π.tt (i - 1) < t → t ≤ π.tt i →
          ∫⁻ ω, (‖X t ω - X (π.tt (i - 1)) ω‖ₑ ^ 2 + ‖Y t ω - Y (π.tt (i - 1)) ω‖ₑ ^ 2) ∂P
            ≤ ENNReal.ofReal (C * (1 + ‖x‖ ^ 2) * π.mesh) := by sorry

end ZhangBSDE.Scheme
