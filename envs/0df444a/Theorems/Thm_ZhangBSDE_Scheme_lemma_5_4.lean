-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_lemma_5_4
-- name    : ZhangBSDE.Scheme.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:35.158004+00:00
-- url     : https://prove2.me/theorems/1ec95767-fdcc-478c-b180-684bb0d8effe
-- title:
--   Lemma 5.4, pp. 479–480 — backward discrete Gronwall: max_i a_i ≤ e^{CT}[a_n + Σ_i b_i]
-- statement:
--   Let $\pi:0=t_0<\dots<t_n=T$ be a partition, $C\ge0$ a constant, and $a_i,b_i$, $i=0,\dots,n$, real numbers with $a_n\ge0$, $b_i\ge0$ and
--   $$a_{i-1}\le(1+C\Delta t_i)\,a_i+b_i,\qquad i=1,\dots,n .$$
--   Then
--   $$\max_{0\le i\le n}a_i\le e^{CT}\Big[a_n+\sum_{i=1}^n b_i\Big].$$
--
--   This discrete Gronwall inequality, run backward in time, is applied to the one-step error recursion of the backward scheme in the proof of Theorem 5.3.
--
--   **Formalization Note** The maximum is stated as a bound for every $i\le n$. The hypothesis $C\ge0$ is added: the paper's $C$ is its generic positive constant, and for $C<0$ the conclusion fails already at $i=n$ when $a_n>0$.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Lemma 5.4, pp. 479–480

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_Setting

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Lemma 5.4 (pp. 479–480), a backward discrete Gronwall inequality: for a partition
`π : 0 = t_0 < ⋯ < t_n = T`, a constant `C ≥ 0` and reals `a_i, b_i` (`i = 0, …, n`) with `a_n ≥ 0`,
`b_i ≥ 0` and `a_{i−1} ≤ (1 + C Δt_i) a_i + b_i` for `i = 1, …, n`,
`max_{0≤i≤n} a_i ≤ e^{CT} [a_n + Σ_{i=1}^n b_i]`. -/
theorem lemma_5_4 {T : ℝ≥0} (π : Partition T) (C : ℝ) (hC : 0 ≤ C) (a b : ℕ → ℝ)
    (ha : 0 ≤ a π.n) (hb : ∀ i ≤ π.n, 0 ≤ b i)
    (hrec : ∀ i ∈ Finset.Icc 1 π.n, a (i - 1) ≤ (1 + C * π.Δt i) * a i + b i) :
    ∀ i ≤ π.n, a i ≤ Real.exp (C * T) * (a π.n + ∑ j ∈ Finset.Icc 1 π.n, b j) := by sorry

end ZhangBSDE.Scheme
