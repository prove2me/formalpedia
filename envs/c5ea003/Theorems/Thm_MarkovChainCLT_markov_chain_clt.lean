-- Prove2me | Theorems.Thm_MarkovChainCLT_markov_chain_clt
-- name    : MarkovChainCLT.markov_chain_clt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:42:56.864515+00:00
-- url     : https://prove2.me/theorems/5272151d-f026-43e0-8005-adeb395e6ff8
-- title:
--   The Markov chain CLT: six sufficient conditions (Jones Thm 9, mission goal)
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$, Harris ergodic with invariant probability distribution $\pi$, and let $f : \mathsf{X} \to \mathbb{R}$ be measurable. Write $\bar f_n = n^{-1} \sum_{i=1}^{n} f(X_i)$ for the sample average and $E_\pi f = \int f \, d\pi$. Assume one of the following six conditions:
--
--   1. the chain is polynomially ergodic of order $m > 1$ with $E_\pi M < \infty$ for the rate constant $M$, and $|f| < B$ $\pi$-almost surely for some $B$;
--   2. the chain is polynomially ergodic of order $m$ with $E_\pi M < \infty$, and $E_\pi |f|^{2+\delta} < \infty$ for some $\delta > 0$ with $m\delta > 2 + \delta$;
--   3. the chain is geometrically ergodic and $E_\pi |f|^{2+\delta} < \infty$ for some $\delta > 0$;
--   4. the chain is geometrically ergodic and $E_\pi [f^2 \log^+ |f|] < \infty$;
--   5. the chain is geometrically ergodic, reversible with respect to $\pi$ (detailed balance), and $E_\pi f^2 < \infty$;
--   6. the chain is uniformly ergodic and $E_\pi f^2 < \infty$.
--
--   Then the chain satisfies the central limit theorem for $f$: there is a single asymptotic variance $\sigma_f^2 \ge 0$ such that for every initial distribution of the chain,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma_f^2) \qquad (n \to \infty).
--   $$
--
--   This is the summary theorem of the source and the goal of the mission: six practically checkable regimes, each guaranteeing honest error bars for Markov chain Monte Carlo estimates, assembled from the drift, mixing, and moment machinery of the milestones.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4, Theorem 9, the summary theorem (arXiv v2 p. 13)

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 9** (the mission goal; Jones 2004, §4): let `X` be a Harris ergodic
Markov chain with invariant distribution `π` and `f` a Borel function.  If one of
the following six conditions holds:

1. `X` is polynomially ergodic of order `m > 1` with `E_π M < ∞` and `|f| < B`
   `π`-almost surely;
2. `X` is polynomially ergodic of order `m` with `E_π M < ∞` and
   `E_π |f|^{2+δ} < ∞` where `mδ > 2+δ`;
3. `X` is geometrically ergodic and `E_π |f|^{2+δ} < ∞` for some `δ > 0`;
4. `X` is geometrically ergodic and `E_π [f² log⁺|f|] < ∞`;
5. `X` is geometrically ergodic, satisfies detailed balance, and `E_π f² < ∞`;
6. `X` is uniformly ergodic and `E_π f² < ∞`;

then for every initial distribution `√n (f̄_n - E_π f) →d N(0, σ_f²)`. -/

theorem MarkovChainCLT.markov_chain_clt {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hcase :
      (∃ m : ℝ, 1 < m ∧ PolynomiallyErgodicL1 P π m ∧
        ∃ B : ℝ, ∀ᵐ x ∂π, |f x| < B) ∨
      (∃ m δ : ℝ, 0 < δ ∧ 2 + δ < m * δ ∧ PolynomiallyErgodicL1 P π m ∧
        Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (GeometricallyErgodic P π ∧
        ∃ δ : ℝ, 0 < δ ∧ Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (GeometricallyErgodic P π ∧
        Integrable (fun x => f x ^ 2 * Real.posLog |f x|) π) ∨
      (GeometricallyErgodic P π ∧ Kernel.IsReversible P π ∧ MemLp f 2 π) ∨
      (UniformlyErgodic P π ∧ MemLp f 2 π)) :
    SatisfiesCLT P π f := by sorry
