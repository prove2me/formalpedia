-- Prove2me | Theorems.Thm_YuStrategic_Optimality_theorem_3_3
-- name    : YuStrategic.Optimality.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:27:32.635201+00:00
-- url     : https://prove2.me/theorems/9af3a9e7-1904-4b18-b6ad-380b04ab371e
-- title:
--   Theorem 3.3 — $\phi^*$ is lower semianalytic and one policy is $\epsilon$-optimal at every state (corrected: $E^*$ over $\tilde{\mathcal S}'_\star$ in (iii))
-- statement:
--   Consider the Borel-space MDP with analytic constraint graph $\Gamma$ and Borel transition kernel $q$. Let $(\mathcal S_\star,\Pi_\star)=(\mathcal S,\Pi)$, $(\mathcal S_m,\Pi_{sm})$ or $(\mathcal S_s,\Pi_{ss})$, and let $\phi:\tilde{\mathcal S}_\star\to\bar{\mathbb R}$ be lower semianalytic. Then:
--   1. (i) The function $\phi^*(x):=\inf_{p\in\tilde{\mathcal S}_\star(x)}\phi(x,p)$, $x\in\mathbb X$, is lower semianalytic.
--   2. (ii) For each $\epsilon>0$ there exists a policy $\pi^*\in\Pi_\star$ such that
--   $$\phi(x,\rho_x[\pi^*])=\phi^*(x)\qquad\forall\,x\in E^*:=\Big\{x\in\mathbb X\ \Big|\ \operatorname*{arg\,min}_{p\in\tilde{\mathcal S}_\star(x)}\phi(x,p)\ne\varnothing\Big\}, \tag{3.3}$$
--   $$\phi(x,\rho_x[\pi^*])\le\begin{cases}\phi^*(x)+\epsilon&\text{if }\phi^*(x)>-\infty,\\-1/\epsilon&\text{if }\phi^*(x)=-\infty,\end{cases}\qquad\forall\,x\in\mathbb X\setminus E^*. \tag{3.4}$$
--   3. (iii) If $\phi^*(x)=\inf_{p\in\tilde{\mathcal S}'_\star(x)}\phi(x,p)$ for all $x\in\mathbb X$, then for each $\epsilon>0$ the policy $\pi^*\in\Pi_\star$ in (ii) can be taken to be nonrandomized, satisfying (3.3)–(3.4) with $E^*$ replaced by $E^{*\prime}:=\{x\mid\operatorname{arg\,min}_{p\in\tilde{\mathcal S}'_\star(x)}\phi(x,p)\ne\varnothing\}$.
--   4. (iii, continued) For $\mathcal S_\star=\mathcal S$ or $\mathcal S_m$, the condition of (iii) holds if for each $\pi\in\Pi$ or $\Pi_m$, respectively,
--   $$\phi(x,\rho_x[\pi])\ge\int_{[0,1]^\infty}\phi\big(x,\rho_x[\bar f(\bar\theta)]\big)\,\bar\lambda(d\bar\theta)\qquad\forall\,x\in\mathbb X, \tag{3.5}$$
--   where $\bar f(\bar\theta)$ is a family associated with $\pi$ as in Theorem 3.2.
--
--   The point of the theorem is that one policy $\pi^*$ is optimal or $\epsilon$-optimal at **every** initial state, not merely almost everywhere with respect to a given measure on $\mathbb X$, for an arbitrary lower semianalytic criterion of the strategic measure.
--
--   **Correction to (iii).** As printed, (iii) asks the nonrandomized $\pi^*$ to satisfy (3.3) on $E^*$, which is defined with $\tilde{\mathcal S}_\star$. This can fail: take one state $x$, actions $[0,1]$, $\Gamma=\mathbb X\times\mathbb A$, and $\phi(x,p)=g(\gamma_0(p))$ with $\gamma_0(p)$ the law of $a_0$ under $p$ and $g$ the Borel function with $g(\tfrac12\delta_0+\tfrac12\delta_1)=0$, $g(\delta_a)=|a-\tfrac12|$ for $a\ne\tfrac12$, and $g=1$ elsewhere. Then $\phi^*(x)=0=\inf_{\tilde{\mathcal S}'_\star(x)}\phi$, so the condition of (iii) holds and $x\in E^*$, but no nonrandomized policy attains $0$. The paper's proof ("replace $\tilde{\mathcal S}_\star$ with $\tilde{\mathcal S}'_\star$ in the preceding proof") gives (3.3) on $E^{*\prime}\subseteq E^*$, as stated in 3.
--
--   Differences from the source:
--   - correction: (iii) the nonrandomized $\pi^*$ satisfies (3.3) on $E^*$ (argmin over $\tilde{\mathcal S}_\star(x)$) → it satisfies (3.3) on $E^{*\prime}$ (argmin over $\tilde{\mathcal S}'_\star(x)$) and (3.4) off $E^{*\prime}$; reason: the printed statement is false — one state, actions $[0,1]$, $\phi(x,p)=g(\text{law of }a_0)$ with $g(\tfrac12\delta_0+\tfrac12\delta_1)=0$, $g(\delta_a)=|a-\tfrac12|$ ($a\ne\tfrac12$), $g=1$ elsewhere: the condition of (iii) holds and $x\in E^*$, but no nonrandomized policy attains $\phi^*(x)=0$; the paper's proof yields the corrected form
--   - reading: "the function $\bar f(\bar\theta)$ associated with $\pi$ as given in Theorem 3.2" in (3.5) → some family $\bar f$ with all properties of Theorem 3.2 satisfies (3.5); reason: requiring (3.5) for every such family would be a stronger hypothesis and a weaker theorem, and the proof uses only $\bar f(\bar\theta)\in\Pi'$ (resp. $\Pi'_m$)
--   - reading: "π* can be taken to be nonrandomized" → there is a nonrandomized $\pi^*\in\Pi_\star$ with the optimality properties; reason: the stronger reading, the one the proof gives
--   - encoding: $\phi:\tilde{\mathcal S}_\star\to\bar{\mathbb R}$ lower semianalytic → $\phi$ on $\mathbb X\times\mathcal P(\Omega)$ whose restriction to $\tilde{\mathcal S}_\star$ is lower semianalytic (Bertsekas–Shreve Def. 7.21, levels $<c$); reason: values off $\tilde{\mathcal S}_\star$ never enter $\phi^*$, $E^*$ or the conclusions, and the $<c$ and $\le r$ forms are equivalent
--   - encoding: the integral in (3.5) of a possibly non-integrable function → $\int g^+\,d\bar\lambda-\int g^-\,d\bar\lambda$ with $\infty-\infty=+\infty$ (`extIntegral`, lower Lebesgue integrals); reason: the paper's convention for integrals of extended-real functions (p. 4)
--   - encoding: the integrand $\phi(x,\rho_x[\bar f(\bar\theta)])$ → $\inf\{\phi(x,P')\mid P'=\rho_x[\bar f(\bar\theta)]\}$; reason: the strategic measure exists and is unique, so the infimum is over one point
--   - encoding: $\rho_x[\pi^*]$ → every $P$ with `IsStrategicMeasure π* δₓ P`, required to exist; reason: the strategic measure exists and is unique
--   - encoding: Borel/weak-topology structure on $\mathcal P(\Omega)$ → Mathlib's weak-convergence topology and $\sigma$-algebra generated by $p\mapsto p(B)$; reason: they coincide for Borel spaces
--   - encoding: Markov, semi-Markov, stationary and semi-stationary policies as kernels depending only on $x_n$ or $(x_0,x_n)$ → kernels factoring through universally measurable kernels on $\mathbb A$ given $\mathbb X$ or $\mathbb X^2$; reason: the two descriptions give the same policies
--   - encoding: analytic sets as the empty set or images of Borel subsets of Polish spaces under Borel maps (p. 5) → Mathlib's `AnalyticSet` (empty or a continuous image of the Baire space); reason: the two agree for subsets of a Borel space (Bertsekas–Shreve Prop. 7.41)
--   - encoding: $\rho_{p_0}[\pi]$ as the restriction of $\mathbb P^\pi_{p_0}$ to $\mathcal B(\Omega)$ → the predicate `IsStrategicMeasure M π p₀ P` ($x_0\sim p_0$, $a_n$ given $h_n$ follows $\mu_n$, $x_{n+1}$ given $h_n'$ follows $q$); reason: the predicate characterizes exactly that measure (compare Lemma 5.1), which exists and is unique by the milestone `strategicMeasure_existsUnique`
--   - generalization: the model includes a lower semianalytic one-stage cost $c$ → the model has no cost; reason: the theorem does not involve $c$, so every model of the paper is an instance
-- source:
--   Yu, On Strategic Measures and Optimality Properties in Discrete-Time Stochastic Control with Universally Measurable Policies, arXiv:2206.06492v3, Theorem 3.3, pp. 8–9, eqs. (3.3)–(3.5)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_LowerSemianalytic
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_ImperfectInfo_Foundations
import Definitions.Def_YuStrategic_Optimality_StrategicSets
import Definitions.Def_YuStrategic_Optimality_Mixture
import Definitions.Def_YuStrategic_Optimality_Optimization

namespace YuStrategic.Optimality

open MeasureTheory BertsekasShreve.AnalyticSelection

/-- **Theorem 3.3** (Yu, arXiv:2206.06492v3, pp. 8–9). Let `(S⋆, Π⋆) = (S, Π), (S_m, Π_sm)` or
`(S_s, Π_ss)` and let `φ : S̃⋆ → R̄` be lower semianalytic. Then:
1. (i) `φ*(x) := inf_{p ∈ S̃⋆(x)} φ(x, p)`, `x ∈ X`, is lower semianalytic.
2. (ii) For each `ε > 0` there is one policy `π* ∈ Π⋆` such that, for every `x ∈ X`,
   `φ(x, ρₓ[π*]) = φ*(x)` if `x ∈ E* := {x | arg min_{p ∈ S̃⋆(x)} φ(x, p) ≠ ∅}` (3.3), and
   `φ(x, ρₓ[π*]) ≤ φ*(x) + ε` if `φ*(x) > −∞`, `≤ −1/ε` if `φ*(x) = −∞`, for `x ∉ E*` (3.4).
3. (iii) If `φ*(x) = inf_{p ∈ S̃′⋆(x)} φ(x, p)` for all `x`, then for each `ε > 0` the policy `π*`
   can be taken nonrandomized, satisfying (3.3)–(3.4) with `E*` replaced by
   `E*′ := {x | arg min_{p ∈ S̃′⋆(x)} φ(x, p) ≠ ∅}` (corrected; see below).
4. (iii, last statement) For `S⋆ = S` or `S_m`, that condition holds if for each `π ∈ Π` (resp.
   `Π_m`), `φ(x, ρₓ[π]) ≥ ∫_{[0,1]^∞} φ(x, ρₓ[f̄(θ̄)]) λ̄(dθ̄)` for all `x` (3.5), with `f̄` associated
   with `π` as in Theorem 3.2.

**Correction.** As printed, (iii) asks the nonrandomized `π*` to satisfy (3.3) on `E*`, which is
defined with `S̃⋆`. That is false: with one state `x`, actions `[0, 1]`, `Γ = X × A`, and
`φ(x, p) = f(law of a₀ under p)` for the Borel `f` with `f((δ₀ + δ₁)/2) = 0`, `f(δₐ) = |a − 1/2|`
(`a ≠ 1/2`) and `f = 1` elsewhere, `φ*(x) = 0 = inf_{S̃′(x)} φ` is attained only by randomized
policies, so `x ∈ E*` but no nonrandomized policy attains it. The paper's proof ("replace `S̃⋆`
with `S̃′⋆` in the preceding proof") yields (3.3) on `E*′ ⊆ E*`, which is what is stated here.

**Formalization Note.**
1. `φ` is a function on all of `X × P(Ω)`; "lower semianalytic on `S̃⋆`" is
   `IsLowerSemianalytic (stratSetTilde M κ) φ` (Bertsekas–Shreve Def. 7.21, levels `< c`, equivalent
   to the page's `≤ r`). Values off `S̃⋆` never enter `φ*`, `E*` or the conclusions.
2. `φ*` is `phiStar`, an infimum in `EReal`; `E*`, `E*′` are `argminSet`.
3. `ρₓ[π]` is "the `P` with `IsStrategicMeasure M π δₓ P`"; `IsEpsOptimalEverywhere` also requires it to
   exist. One `π*` serves every `x` (`∃ π*, ∀ x`).
4. `Π⋆` is `κ.semiMem` and `S⋆` is `κ.mem`.
5. In (3.5), "`f̄` as given in Theorem 3.2" is read as: some family `f̄` with all properties of
   Theorem 3.2 (`IsMixtureFamily`) satisfies (3.5). The integral is the extended integral
   `∫ g⁺ dλ̄ − ∫ g⁻ dλ̄` with `∞ − ∞ = +∞` (p. 4), `BertsekasShreve.ImperfectInfo.extIntegral`, and
   the integrand `φ(x, ρₓ[f̄(θ̄)])` is written `⨅ P' with IsStrategicMeasure (f̄ θ̄) δₓ P', φ(x, P')`,
   which is `φ(x, ρₓ[f̄(θ̄)])` because the strategic measure exists and is unique. -/
theorem theorem_3_3 {X A : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [IsBorelSpace X] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [IsBorelSpace A]
    (M : Model X A) (κ : PolicyClass) (φ : X × ProbabilityMeasure (Path X A) → EReal)
    (hφ : IsLowerSemianalytic (stratSetTilde M κ) (fun z => φ z)) :
    BertsekasShreve.BorelInfinite.IsLowerSemianalyticFun (phiStar (stratSetTilde M κ) φ) ∧
    (∀ ε : ℝ, 0 < ε → ∃ π : Policy M, κ.semiMem π ∧
      IsEpsOptimalEverywhere M φ (phiStar (stratSetTilde M κ) φ)
        (argminSet (stratSetTilde M κ) φ) ε π) ∧
    ((∀ x, phiStar (stratSetTilde M κ) φ x = phiStar (stratSetTilde' M κ) φ x) →
      ∀ ε : ℝ, 0 < ε → ∃ π : Policy M, κ.semiMem π ∧ π.IsNonrandomized ∧
        IsEpsOptimalEverywhere M φ (phiStar (stratSetTilde M κ) φ)
          (argminSet (stratSetTilde' M κ) φ) ε π) ∧
    ((κ = .all ∨ κ = .markov) →
      (∀ π : Policy M, κ.mem π → ∃ fbar : (ℕ → unitInterval) → Policy M,
        IsMixtureFamily M π fbar ∧
        ∀ (x : X) (P : ProbabilityMeasure (Path X A)), IsStrategicMeasure M π (diracPM x) P →
          BertsekasShreve.ImperfectInfo.extIntegral lambdaBar
              (fun θ => ⨅ (P' : ProbabilityMeasure (Path X A))
                (_ : IsStrategicMeasure M (fbar θ) (diracPM x) P'), φ (x, P')) ≤ φ (x, P)) →
      ∀ x, phiStar (stratSetTilde M κ) φ x = phiStar (stratSetTilde' M κ) φ x) := by sorry

end YuStrategic.Optimality
