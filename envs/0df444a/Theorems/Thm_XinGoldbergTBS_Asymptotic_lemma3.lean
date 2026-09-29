-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma3
-- name    : XinGoldbergTBS.Asymptotic.lemma3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:26:10.091969+00:00
-- url     : https://prove2.me/theorems/4c4e0a48-33ad-4225-9cca-9dccb7b81808
-- title:
--   Lemma 3 — Bellman equation and structure of $V^n_\alpha$
-- statement:
--   (JSS, Scarf 1960.) For all $\alpha \in (0,1)$, $r, x \in \mathbb R$ and $n \ge 1$,
--   $$V^n_\alpha(r,x) = \inf_{y \ge x}\Big(\mathbb E\Big[G\Big(y - \sum_{k=n}^{L_0+n}(D_k - r)\Big)\Big] + \alpha\,\mathbb E\big[V^{n-1}_\alpha\big(r, y - (D_{L_0+n} - r)\big)\big]\Big).$$
--   Furthermore:
--   1. for each fixed $n \ge 1$ and $r$, $V^n_\alpha(r,\cdot)$ is a (finite) convex function of $x$ on $\mathbb R$;
--   2. for each fixed $n \ge 1$ and $x$, $V^n_\alpha(\cdot, x)$ is continuous in $r$;
--   3. for each fixed $n \ge 1$ and $r$, $V^n_\alpha(r, \cdot)$ is nondecreasing in $x$;
--   4. for each fixed $x, r$, $V^n_\alpha(r,x)$ is nondecreasing in $n$;
--   5. the infinite-horizon problem (6) admits an optimal stationary Markov policy: a single measurable rule $f$ such that, from every initial position $x$, ordering $f(x_i)$ in every period attains $V^\infty_\alpha(r,x)$.
--
--   These are the classical structural properties of the backlog inventory problem, which the paper quotes (they carry over to possibly negative demand).
--
--   **Formalization Note** The paper's "increasing" is read as nondecreasing (weak), since $V^n_\alpha(r,\cdot)$ is an infimum over $y \ge x$ and Lemma 4 says "nondecreasing" for the same property. "Convex (and thus continuous) function of $x$ on $\mathbb R$" is read as including finiteness, stated explicitly. Values are in $[0,\infty]$; convexity and continuity are stated for the real values.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 444, Lemma 3 (from JSS and Scarf 1960)

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Lemma 3 (JSS, Scarf 1960), p. 444: the Bellman equation for `V^n_α`; convexity (with
finiteness) and monotonicity in `x`, continuity in `r`, monotonicity in `n`; and an optimal
stationary Markov policy for the infinite-horizon problem (6). -/
theorem lemma3 (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ (r x : ℝ) (n : ℕ), 1 ≤ n →
      Vn μ κ L₀ α n r x =
        ⨅ (y : ℝ) (_ : x ≤ y),
          (∫⁻ d, ENNReal.ofReal
              (G κ (y - ∑ k ∈ Finset.range (L₀ + 1), (d (n - 1 + k) - r))) ∂pathLaw μ +
            ENNReal.ofReal α *
              ∫⁻ d, Vn μ κ L₀ α (n - 1) r (y - (d (L₀ + n - 1) - r)) ∂pathLaw μ)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ r x : ℝ, Vn μ κ L₀ α n r x ≠ ⊤) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ r : ℝ,
      ConvexOn ℝ Set.univ (fun x => (Vn μ κ L₀ α n r x).toReal)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ x : ℝ, Continuous (fun r => (Vn μ κ L₀ α n r x).toReal)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ r : ℝ, Monotone (fun x => Vn μ κ L₀ α n r x)) ∧
    (∀ r x : ℝ, Monotone (fun n : ℕ => Vn μ κ L₀ α n r x)) ∧
    (∀ r : ℝ, ∃ f : ℝ → ℝ≥0, ∀ x : ℝ, ∃ π : SSPolicy, IsStationaryMarkov π f r x ∧
      ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ = Vinf μ κ L₀ α r x) := by sorry

end XinGoldbergTBS.Asymptotic
