-- Prove2me | Theorems.Thm_YuStrategic_Optimality_corollary_5_1_i
-- name    : YuStrategic.Optimality.corollary_5_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:26:30.042571+00:00
-- url     : https://prove2.me/theorems/f735e6ca-4ffd-4845-a7bb-61322f259b45
-- title:
--   Corollary 5.1(i) — $\mathcal S$ is cut out by the control constraint (5.2) and the dynamics (5.3)
-- statement:
--   In the Borel-space MDP with analytic constraint graph $\Gamma$ and Borel transition kernel $q$, a probability measure $p\in\mathcal P(\Omega)$ is a strategic measure, $p\in\mathcal S$, if and only if
--   $$p\{(x_n,a_n)\in\Gamma\}=1\qquad\forall\,n\ge0, \tag{5.2}$$
--   $$Q_n(dx_{n+1}\mid h_n';p)=q(dx_{n+1}\mid x_n,a_n)\quad\forall\,n\ge0,\ \ p\text{-almost surely}, \tag{5.3}$$
--   where $Q_n(dx_{n+1}\mid h'_n;p)$ is a conditional distribution of $x_{n+1}$ given $h'_n=(x_0,a_0,\dots,x_n,a_n)$ under $p$. That is,
--   $$\mathcal S=\{p\in\mathcal P(\Omega)\mid p\text{ satisfies (5.2)–(5.3)}\}.$$
--
--   Condition (5.2) is the control constraint and (5.3) the state transition dynamics; no condition on the conditional law of the actions is needed. This description is the starting point of the proof that $\mathcal S$ is analytic (Theorem 3.1).
--
--   Differences from the source:
--   - encoding: (5.3) for a chosen version $Q_n$ of the conditional distribution → $p\{h'_n\in B,\ x_{n+1}\in C\}=\int_{\{h'_n\in B\}}q(C\mid x_n,a_n)\,dp$ for all Borel $B\subseteq H'_n$, $C\subseteq\mathbb X$; reason: this says $q(\cdot\mid x_n,a_n)$ is itself a version of the conditional distribution, and any two versions agree $p$-a.s. because $\mathcal B(\mathbb X)$ is countably generated
--   - encoding: $p\{(x_n,a_n)\in\Gamma\}$ for the analytic event, w.r.t. the completion of $p$ → Mathlib's (outer) measure of the event; reason: the event is universally measurable, where the outer measure equals the completion's value
--   - encoding: analytic sets as the empty set or images of Borel subsets of Polish spaces under Borel maps (p. 5) → Mathlib's `AnalyticSet` (empty or a continuous image of the Baire space); reason: the two agree for subsets of a Borel space (Bertsekas–Shreve Prop. 7.41)
--   - encoding: $\rho_{p_0}[\pi]$ as the restriction of $\mathbb P^\pi_{p_0}$ to $\mathcal B(\Omega)$ → the predicate `IsStrategicMeasure M π p₀ P` ($x_0\sim p_0$, $a_n$ given $h_n$ follows $\mu_n$, $x_{n+1}$ given $h_n'$ follows $q$); reason: the predicate characterizes exactly that measure (compare Lemma 5.1), which exists and is unique by the milestone `strategicMeasure_existsUnique`
--   - generalization: the model includes a lower semianalytic one-stage cost $c$ → the model has no cost; reason: the statement does not involve $c$, so every model of the paper is an instance
-- source:
--   Yu, arXiv:2206.06492v3, Corollary 5.1(i), p. 26, with conditions (5.2)–(5.3), p. 25 and Q_n defined on p. 23

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_YuStrategic_Optimality_StrategicSets

namespace YuStrategic.Optimality

open MeasureTheory BertsekasShreve.AnalyticSelection BertsekasShreve.BorelInfinite

/-- **Corollary 5.1(i)** (Yu, arXiv:2206.06492v3, p. 26, with (5.2)–(5.3) on p. 25). The set `S` of
all strategic measures consists exactly of the `p ∈ P(Ω)` that satisfy
1. (5.2) `p{(xₙ, aₙ) ∈ Γ} = 1` for all `n ≥ 0` (the control constraint), and
2. (5.3) `Qₙ(dxₙ₊₁ | h′ₙ; p) = q(dxₙ₊₁ | xₙ, aₙ)` `p`-almost surely for all `n ≥ 0`, where `Qₙ` is a
   conditional distribution of `xₙ₊₁` given `h′ₙ` w.r.t. `p` (the state transition dynamics).

**Formalization Note.** (5.3) is written without choosing `Qₙ`: it says that `q(· | xₙ, aₙ)` is a
version of the conditional distribution of `xₙ₊₁` given `h′ₙ = (hₙ, aₙ)`, i.e.
`p{h′ₙ ∈ B, xₙ₊₁ ∈ C} = ∫_{h′ₙ ∈ B} q(C | xₙ, aₙ) dp` for all Borel `B ⊆ H′ₙ`, `C ⊆ X`. Two conditional
distributions agree `p`-a.s. (`X` is countably generated), so this is equivalent for every choice of
`Qₙ`. The event `{(xₙ, aₙ) ∈ Γ}` is analytic, and `p` evaluated at it is the completion's value. -/
theorem corollary_5_1_i {X A : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [IsBorelSpace X] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [IsBorelSpace A]
    (M : Model X A) :
    stratSet M .all =
      {P : ProbabilityMeasure (Path X A) |
        (∀ n : ℕ, (P : Measure (Path X A)) {ω | (stateAt n ω, actAt n ω) ∈ M.graph} = 1) ∧
        ∀ (n : ℕ) (B : Set (Hist X A n × A)) (C : Set X), MeasurableSet B → MeasurableSet C →
          (P : Measure (Path X A)) {ω | (histAt n ω, actAt n ω) ∈ B ∧ stateAt (n + 1) ω ∈ C} =
            ∫⁻ ω in {ω | (histAt n ω, actAt n ω) ∈ B}, M.q (stateAt n ω, actAt n ω) C
              ∂(P : Measure (Path X A))} := by sorry

end YuStrategic.Optimality
