-- Prove2me | Theorems.Thm_YuStrategic_Optimality_strategicMeasure_existsUnique
-- name    : YuStrategic.Optimality.strategicMeasure_existsUnique
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:25:12.075685+00:00
-- url     : https://prove2.me/theorems/30de63c9-f895-4819-82ca-fbd57a77416d
-- title:
--   §2.2 — a policy and an initial distribution determine a unique strategic measure $\rho_{p_0}[\pi]$
-- statement:
--   Let $\mathbb X,\mathbb A$ be Borel spaces and consider the Borel-space MDP with analytic constraint graph $\Gamma$ and Borel transition kernel $q$. For every universally measurable policy $\pi=(\mu_n)_{n\ge0}$ and every initial state distribution $p_0\in\mathcal P(\mathbb X)$, there is exactly one probability measure $p$ on $\mathcal B(\Omega)$ such that
--   1. $x_0\sim p_0$;
--   2. $p\{h_n\in B,\ a_n\in C\}=\int_{\{h_n\in B\}}\mu_n(C\mid h_n)\,dp$ for all $n$ and Borel $B,C$;
--   3. $p\{h_n'\in B,\ x_{n+1}\in C\}=\int_{\{h_n'\in B\}}q(C\mid x_n,a_n)\,dp$ for all $n$ and Borel $B,C$.
--
--   This $p$ is the strategic measure $\rho_{p_0}[\pi]$: the probability measure determined by $p_0$ and the kernels $\mu_0(da_0\mid x_0),q(dx_1\mid x_0,a_0),\mu_1(da_1\mid h_1),\dots$ (the paper cites Bertsekas–Shreve, Prop. 7.45). It is what makes "$\rho_x[\pi]$" well defined in all later statements.
--
--   Differences from the source:
--   - encoding: the unique probability measure $\mathbb P^\pi_{p_0}$ on $\mathcal U(\Omega)$ determined by the kernels → the unique $P$ on $\mathcal B(\Omega)$ satisfying the finite-dimensional conditions 1–3 (`IsStrategicMeasure`); reason: a measure on $\mathcal U(\Omega)$ is determined by its restriction to $\mathcal B(\Omega)$ (p. 7), and conditions 1–3 are the defining property of the kernel composition (compare Lemma 5.1)
--   - encoding: integrals of universally measurable integrands w.r.t. the completion of $p$ → Mathlib lower Lebesgue integrals w.r.t. $p$; reason: the two agree for null-measurable integrands, the convention of p. 4
--   - encoding: analytic sets as the empty set or images of Borel subsets of Polish spaces under Borel maps (p. 5) → Mathlib's `AnalyticSet` (empty or a continuous image of the Baire space); reason: the two agree for subsets of a Borel space (Bertsekas–Shreve Prop. 7.41)
--   - generalization: the model includes a lower semianalytic one-stage cost $c$ → the model has no cost; reason: the statement does not involve $c$, so every model of the paper is an instance
-- source:
--   Yu, On Strategic Measures and Optimality Properties in Discrete-Time Stochastic Control with Universally Measurable Policies, arXiv:2206.06492v3, §2.2, unnumbered, p. 6 (citing [5, Prop. 7.45]); restriction ρ_{p0}[π], p. 7

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_YuStrategic_Optimality_StrategicMeasure

namespace YuStrategic.Optimality

open MeasureTheory BertsekasShreve.AnalyticSelection

/-- **§2.2, unnumbered** (Yu, arXiv:2206.06492v3, p. 6, citing [Bertsekas–Shreve, Prop. 7.45];
restriction to `B(Ω)` on p. 7). For a policy `π ∈ Π` and an initial state distribution
`p₀ ∈ P(X)`, the kernels `μ₀(da₀ | x₀), q(dx₁ | x₀, a₀), μ₁(da₁ | h₁), q(dx₂ | x₁, a₁), …` together
with `p₀` determine a unique probability measure on `Ω`: there is exactly one `P ∈ P(Ω)` that is
the strategic measure `ρ_{p₀}[π]`.

**Formalization Note.** `IsStrategicMeasure M π p₀ P` pins `P` down by its finite-dimensional
laws (the law of `x₀` is `p₀`; `aₙ` given `hₙ` follows `μₙ`; `xₙ₊₁` given `h′ₙ` follows `q`). The
page states the result for the extension `P^π_{p₀}` on the universally measurable sets `U(Ω)`; a
probability measure on `U(Ω)` is determined by its restriction to `B(Ω)` (p. 7), which is the
`P` here. -/
theorem strategicMeasure_existsUnique {X A : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [IsBorelSpace X] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [IsBorelSpace A]
    (M : Model X A) (π : Policy M) (p₀ : ProbabilityMeasure X) :
    ∃! P : ProbabilityMeasure (Path X A), IsStrategicMeasure M π p₀ P := by sorry

end YuStrategic.Optimality
