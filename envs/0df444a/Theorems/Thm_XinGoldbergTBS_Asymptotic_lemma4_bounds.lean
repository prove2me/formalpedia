-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma4_bounds
-- name    : XinGoldbergTBS.Asymptotic.lemma4_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:26:38.292452+00:00
-- url     : https://prove2.me/theorems/00f9d62b-8314-40af-8fc2-cbec6136c4a1
-- title:
--   Lemma 4 (8) — $0 \le V^\infty_\alpha - V^n_\alpha \le \dots\alpha^n$; structure of $V^\infty_\alpha$ and $|S^\infty_\alpha(r)| \le \bar S_\alpha(r)$
-- statement:
--   For $\alpha\in(0,1)$, $r, x \in \mathbb R$ and $n \ge 1$,
--   $$0 \le V^\infty_\alpha(r,x) - V^n_\alpha(r,x) \le \max(b,h)\,\big(\bar S_\alpha(r) + |x| + |r| + \mathbb E[D]\big)(1 + L_0 + n)(1-\alpha)^{-2}\alpha^n, \tag{8}$$
--   and $V^\infty_\alpha(r,x) = \lim_{n\to\infty}V^n_\alpha(r,x)$. Furthermore, for $\alpha \in (0,1)$ and $r \in \mathbb R$:
--   1. $V^\infty_\alpha(r,x)$ is a finite-valued, convex and nondecreasing function of $x$ on $\mathbb R$;
--   2. the set of minimizers in $x$ of $V^\infty_\alpha(r,\cdot)$ is nonempty and bounded above, and its supremum $S^\infty_\alpha(r)$ satisfies $|S^\infty_\alpha(r)| \le \bar S_\alpha(r)$;
--   3. the infinite-horizon problem (6) admits an optimal stationary base-stock policy with order-up-to level $S^\infty_\alpha(r)$.
--
--   Here $\bar S_\alpha(r) = 4(L_0+1)\frac{\max(b,h)}{\min(b,h)}(|r| + \mathbb E[D])(1-\alpha)^{-2}$.
--
--   This controls the finite-horizon value by the infinite-horizon one, whose optimal policy is a base-stock policy.
--
--   **Formalization Note** (8) is stated as $V^n_\alpha \le V^\infty_\alpha \le V^n_\alpha + (\text{bound})$ in $[0,\infty]$. Since the paper states that $V^\infty_\alpha$ is finite, this is equivalent to the difference form. Nonemptiness and boundedness of the minimizer set are implicit in the paper's claim about $S^\infty_\alpha(r)$ and are stated explicitly.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 444, Lemma 4, Eq. (8)

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Lemma 4, p. 444, first part: bound (8) (written additively in `ℝ≥0∞`), `V^∞_α = lim_n V^n_α`,
and finiteness, convexity, monotonicity of `V^∞_α(r, ·)`; its minimizer set is nonempty and
bounded above, `|S^∞_α(r)| ≤ S̄_α(r)`, and the base-stock policy with level `S^∞_α(r)` is optimal
for (6). -/
theorem lemma4_bounds (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ (r x : ℝ) (n : ℕ), 1 ≤ n →
      Vn μ κ L₀ α n r x ≤ Vinf μ κ L₀ α r x ∧
      Vinf μ κ L₀ α r x ≤ Vn μ κ L₀ α n r x +
        ENNReal.ofReal (max κ.b κ.h * (Sbar μ κ L₀ α r + |x| + |r| + μ.mean) *
          (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n)) ∧
    (∀ r x : ℝ, Tendsto (fun n => Vn μ κ L₀ α n r x) atTop (nhds (Vinf μ κ L₀ α r x))) ∧
    (∀ r : ℝ,
      (∀ x : ℝ, Vinf μ κ L₀ α r x ≠ ⊤) ∧
      ConvexOn ℝ Set.univ (fun x => (Vinf μ κ L₀ α r x).toReal) ∧
      Monotone (fun x => Vinf μ κ L₀ α r x) ∧
      (VinfMinimizers μ κ L₀ α r).Nonempty ∧
      BddAbove (VinfMinimizers μ κ L₀ α r) ∧
      |Sinf μ κ L₀ α r| ≤ Sbar μ κ L₀ α r ∧
      ∀ x : ℝ, ∃ π : SSPolicy, IsStationaryMarkov π (baseStockRule (Sinf μ κ L₀ α r)) r x ∧
        ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ = Vinf μ κ L₀ α r x) := by sorry

end XinGoldbergTBS.Asymptotic
