-- Prove2me | Definitions.Def_VectorSpaceOpt_bv_stieltjes
-- name    : VectorSpaceOpt_bv_stieltjes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-24T15:48:32.954726+00:00
-- url     : https://prove2.me/theorems/64868a32-6509-4510-86fd-1ab2a79e83a7
-- title:
--   Bounded variation and the Riemann–Stieltjes integral
-- statement:
--   The interface needed to describe the dual of $C[a,b]$: the total variation of a function on an interval, the normalized space $NBV[a,b]$ of which it is the norm, and the Riemann–Stieltjes integral that pairs the two spaces. The three are introduced together because they are not separately meaningful — the norm on $NBV[a,b]$ *is* the total variation, and the pairing that makes $NBV[a,b]$ the dual of $C[a,b]$ *is* the Riemann–Stieltjes integral.
--
--   ## Total variation
--
--   For a real-valued function $v$ on $[a, b]$, the **total variation** of $v$ is
--
--   $$\operatorname{T.V.}(v) = \sup \sum_{i=1}^{n} |v(t_i) - v(t_{i-1})|,$$
--
--   the supremum over all finite partitions $a = t_0 \le t_1 \le \cdots \le t_n = b$. A function with finite total variation is of **bounded variation**.
--
--   ## The normalized space $NBV[a,b]$
--
--   Representation of a functional on $C[a,b]$ by a function of bounded variation is not unique: the evaluation functional $x \mapsto x(1/2)$ on $C[0,1]$ is represented by any $v$ that is $0$ on $[0, 1/2)$, $1$ on $(1/2, 1]$, and takes any value in between at $1/2$ itself. Restricting to a normalized subspace removes the ambiguity. A function $v$ lies in $NBV[a,b]$ when:
--
--   1. $v$ is of bounded variation on $[a, b]$;
--   2. $v$ vanishes at the left endpoint, $v(a) = 0$;
--   3. $v$ is continuous from the right at every point of $[a, b)$.
--
--   ## The Riemann–Stieltjes integral
--
--   A **tagged partition** of $[a, b]$ consists of points $a = t_0 \le t_1 \le \cdots \le t_n = b$ together with tags $\xi_i \in [t_{i-1}, t_i]$; its **mesh** is $\max_i (t_i - t_{i-1})$ and its Riemann–Stieltjes sum is
--
--   $$S = \sum_{i=1}^{n} x(\xi_i)\,\big(v(t_i) - v(t_{i-1})\big).$$
--
--   A real number $I$ is the Riemann–Stieltjes integral $\int_a^b x\,dv$ when for every $\varepsilon > 0$ there is a $\delta > 0$ such that every tagged partition of mesh less than $\delta$ satisfies $|S - I| \le \varepsilon$. For $x$ continuous and $v$ of bounded variation the integral exists and obeys $\left|\int_a^b x\,dv\right| \le \|x\|\cdot\operatorname{T.V.}(v)$, which is what makes the associated functional bounded.
--
--   **Formalization Note.** Total variation is the real-valued reading of Mathlib's extended-real `eVariationOn`, so it returns $0$ on infinite variation and statements carry an explicit bounded-variation hypothesis. Right continuity at $t$ is continuity within the right ray $[t,\infty)$, required on $[a,b)$. The integral is defined as a *relation* — "$I$ is the integral" — rather than as a function, so no existence claim or junk value is built into it; partitions are indexed by natural numbers with the conditions stated for indices below $n$, and the degenerate case $n = 0$ forces $a = b$ and an empty sum.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.5, pp. 113–115

import Mathlib

/-!
# Bounded variation and the Riemann–Stieltjes integral

The interface needed to describe the dual of `C[a,b]` (Luenberger §5.5): the
total variation of a function on an interval, the normalized space `NBV[a,b]`
whose norm it is, and the Riemann–Stieltjes integral that pairs the two spaces.
-/

/-- The total variation of `v` on `[a, b]`, as a real number.

Built from Mathlib's extended-valued `eVariationOn`; the value is `0` when the
variation is infinite, so statements about it carry a bounded-variation
hypothesis. This is the norm on `BV[a,b]` and on `NBV[a,b]`. -/
noncomputable def VectorSpaceOpt_total_variation (v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (eVariationOn v (Set.Icc a b)).toReal

/-- `v` belongs to the *normalized* space of functions of bounded variation
`NBV[a, b]` when it has bounded variation on `[a, b]`, vanishes at `a`, and is
continuous from the right on `[a, b)`. Normalization is what makes the
representation of a functional on `C[a, b]` unique; the norm on this space is
`VectorSpaceOpt_total_variation`. -/
structure VectorSpaceOpt_is_nbv (a b : ℝ) (v : ℝ → ℝ) : Prop where
  boundedVariation : BoundedVariationOn v (Set.Icc a b)
  vanishes_at_left : v a = 0
  right_continuous : ∀ t ∈ Set.Ico a b, ContinuousWithinAt v (Set.Ici t) t

/-- `I` is the Riemann–Stieltjes integral `∫_a^b x dv`.

A tagged partition of `[a, b]` is a finite sequence `a = t 0 ≤ t 1 ≤ ⋯ ≤ t n = b`
together with tags `ξ i ∈ [t i, t (i+1)]`; its Riemann–Stieltjes sum is
`∑ x (ξ i) * (v (t (i+1)) - v (t i))`. The integral is `I` when these sums are
within `ε` of `I` for every tagged partition of mesh less than `δ`. -/
def VectorSpaceOpt_is_rs_integral (x v : ℝ → ℝ) (a b I : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (n : ℕ) (t ξ : ℕ → ℝ),
    t 0 = a → t n = b →
    (∀ i < n, t i ≤ t (i + 1)) →
    (∀ i < n, t (i + 1) - t i < δ) →
    (∀ i < n, t i ≤ ξ i ∧ ξ i ≤ t (i + 1)) →
    |(∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i))) - I| ≤ ε


