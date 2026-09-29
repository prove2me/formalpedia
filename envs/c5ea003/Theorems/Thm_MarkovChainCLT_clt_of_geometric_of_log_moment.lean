-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_geometric_of_log_moment
-- name    : MarkovChainCLT.clt_of_geometric_of_log_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:41:08.709854+00:00
-- url     : https://prove2.me/theorems/4ce4e8ed-1572-48f0-a21d-0515e51d79e4
-- title:
--   Geometric ergodicity CLT under $E_\pi[f^2 \log^+|f|] < \infty$ (Jones Cor 3)
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$, Harris ergodic with invariant probability distribution $\pi$, and let $f : \mathsf{X} \to \mathbb{R}$ be measurable. Write $\bar f_n = n^{-1} \sum_{i=1}^{n} f(X_i)$ for the sample average and $E_\pi f = \int f \, d\pi$. Suppose the chain is geometrically ergodic and
--
--   $$
--   E_\pi\bigl[f^2 \, \log^+ |f|\bigr] < \infty, \qquad \log^+ t = \max(0, \log t).
--   $$
--
--   Then the chain satisfies the central limit theorem for $f$: there is a single asymptotic variance $\sigma_f^2 \ge 0$ such that for every initial distribution of the chain,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma_f^2) \qquad (n \to \infty).
--   $$
--
--   This refines the Chan–Geyer condition: for geometrically ergodic chains a logarithmic sliver above square-integrability suffices (and, by the counterexamples cited in the source, a bare second moment does not).
--
--   **Formalization Note** The stated moment already implies $E_\pi f^2 < \infty$, so it is not assumed separately. "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Corollary 3 (arXiv v2 p. 11; proved there from Theorem 6 via Theorem 2(ii))

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Corollary 3**: a geometrically ergodic Harris chain with
`E_π[f² log⁺|f|] < ∞` satisfies the CLT for every initial distribution. -/

theorem MarkovChainCLT.clt_of_geometric_of_log_moment {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hgeo : GeometricallyErgodic P π)
    (hmom : Integrable (fun x => f x ^ 2 * Real.posLog |f x|) π) :
    SatisfiesCLT P π f := by sorry
