-- Prove2me | Definitions.Def_MarkovErgodicity
-- name    : MarkovErgodicity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-15T14:36:02.849852+00:00
-- url     : https://prove2.me/theorems/ce9321a2-7af6-4845-ba27-e925f5af2ab7
-- title:
--   Harris ergodicity; geometric, uniform, and polynomial ergodicity
-- statement:
--   The ergodicity notions of the mission, for a Markov kernel $P$ with invariant probability $\pi$, all expressed through the total variation distance $\|P^n(x, \cdot) - \pi\|$.
--
--   **Harris ergodic**: $\pi$ is an invariant probability measure of $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$.
--
--   **Convergence with rate** $(M, \gamma)$, the source's eq. (3):
--
--   $$
--   \|P^n(x, \cdot) - \pi\| \;\le\; M(x)\, \gamma(n) \qquad \text{for all } x \text{ and all } n \ge 1.
--   $$
--
--   **Geometrically ergodic**: such a rate with $\gamma(n) = t^n$ for some $0 \le t < 1$ and some $M \ge 0$.
--
--   **Uniformly ergodic**: the same with a constant function $M$.
--
--   **Polynomially ergodic of order $m$ with integrable constant**: such a rate with $\gamma(n) = n^{-m}$ and $M \ge 0$ satisfying $E_\pi M < \infty$ (the standing side condition of the source's Corollaries 1–2 and Theorem 9).
--
--   These are the hypotheses under which all chain-level central limit theorems of the mission are stated; the definitions are generic in the kernel and reusable.
--
--   **Formalization Note** Harris ergodicity is encoded by the total-variation characterization above; for a Markov kernel with an invariant probability this is equivalent to the classical definition (aperiodic, $\psi$-irreducible, positive Harris recurrent), the "every $x$" quantifier being exactly the Harris property.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2 (arXiv v2 pp. 3-4), eqs. (2)-(3) and the surrounding definitions

import Definitions.Def_TotalVariationDist
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
Harris ergodicity (via its total-variation characterization) and rates of
convergence: geometric, uniform, and polynomial ergodicity.

Source: Galin L. Jones, *On the Markov Chain Central Limit Theorem*,
Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), §2:
eqs. (2) (Harris ergodic convergence) and (3) (rate `‖Pⁿ(x,·) - π‖ ≤ M(x)γ(n)`),
and the geometric / uniform / polynomial specializations of `γ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace MarkovChainCLT

/-- **Harris ergodicity**, encoded by its total-variation characterization: `π` is an
invariant probability measure of `P` and from **every** starting point `x` the
`n`-step distribution converges to `π` in total variation.  For a Markov kernel this
is equivalent to the classical definition (aperiodic, `ψ`-irreducible, positive
Harris recurrent; Meyn-Tweedie 1993, Ch. 13): the `∀ x` quantifier is exactly what
upgrades almost-everywhere ergodicity to the Harris property.  Use together with
`[IsMarkovKernel P]` and `[IsProbabilityMeasure π]`. -/
def HarrisErgodic {X : Type*} [MeasurableSpace X] (P : Kernel X X) (π : Measure X) :
    Prop :=
  Kernel.Invariant P π ∧
    ∀ x : X, Tendsto (fun n => tvDist ((iterKernel P n) x) π) atTop (𝓝 0)

/-- The chain has total-variation convergence rate `γ` with `x`-dependent constant
`M`: `‖Pⁿ(x, ·) - π‖ ≤ M(x) γ(n)` for all `x` and all `n ≥ 1` (Jones 2004 eq. (3)). -/
def ErgodicWithRate {X : Type*} [MeasurableSpace X] (P : Kernel X X) (π : Measure X)
    (M : X → ℝ) (γ : ℕ → ℝ) : Prop :=
  ∀ x : X, ∀ n : ℕ, 1 ≤ n → tvDist ((iterKernel P n) x) π ≤ M x * γ n

/-- **Geometric ergodicity**: a total-variation rate `γ(n) = tⁿ` for some `t < 1`,
with a nonnegative `x`-dependent constant (Jones 2004, §2). -/
def GeometricallyErgodic {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    (π : Measure X) : Prop :=
  ∃ M : X → ℝ, ∃ t : ℝ, (∀ x, 0 ≤ M x) ∧ 0 ≤ t ∧ t < 1 ∧
    ErgodicWithRate P π M (fun n => t ^ n)

/-- **Uniform ergodicity**: geometric ergodicity with a constant not depending on the
starting point (Jones 2004, §2). -/
def UniformlyErgodic {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    (π : Measure X) : Prop :=
  ∃ R t : ℝ, 0 ≤ R ∧ 0 ≤ t ∧ t < 1 ∧ ErgodicWithRate P π (fun _ => R) (fun n => t ^ n)

/-- **Polynomial ergodicity of order `m` with integrable constant**: a
total-variation rate `γ(n) = n^{-m}` whose `x`-dependent constant `M` satisfies
`E_π M < ∞` (Jones 2004, §2: polynomial ergodicity together with the standing
side condition `E_π M < ∞` used in Corollaries 1-2 and Theorem 9). -/
def PolynomiallyErgodicL1 {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    (π : Measure X) (m : ℝ) : Prop :=
  ∃ M : X → ℝ, (∀ x, 0 ≤ M x) ∧ Integrable M π ∧
    ErgodicWithRate P π M (fun n => (n : ℝ) ^ (-m))

end MarkovChainCLT


