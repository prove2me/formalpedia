-- Prove2me | Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
-- name    : MarkovChainCLT.isStrictlyStationary_comp_of_measurable
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T15:51:02.72245+00:00
-- url     : https://prove2.me/theorems/423661d4-a255-4399-9bc2-c544254c400e
-- title:
--   Strict stationarity is preserved by a measurable functional
-- statement:
--   Let $Y = \{Y_i\}_{i \ge 0}$ be a sequence of **measurable** random elements of $\mathsf{X}$ which is strictly stationary, and let $g : \mathsf{X} \to \mathsf{E}$ be measurable. Then the functional process $\{g(Y_i)\}_{i \ge 0}$ is strictly stationary.
--
--   Strict stationarity says the law of the shifted path $(Y_k, Y_{k+1}, \dots)$ on the sequence space does not depend on $k$. The coordinatewise map $\Phi : (x_0, x_1, \dots) \mapsto (g(x_0), g(x_1), \dots)$ is measurable, and the path of the functional process is $\Phi$ applied to the path of $Y$. Functoriality of the pushforward, $\Phi_*(\psi_{k})_* P = (\Phi \circ \psi_k)_* P$, then turns the equality of the shifted path laws for $Y$ into the corresponding equality for $g(Y)$.
--
--   **Why measurability of $Y$ is needed.** The pushforward of a non-measurable map is the zero measure by convention, so for a non-measurable $Y$ the stationarity hypothesis degenerates to $0 = 0$ and carries no information, while the conclusion can still be a substantive claim — $g \circ Y_i$ may well be measurable even when $Y_i$ is not (take $\mathsf{X} = \mathbb{R} \times \{0,1\}$, $Y_i = (h, b_i)$ with $h$ non-measurable and $b_i$ measurable, and $g = \mathrm{snd}$). One can then choose $\{b_i\}$ non-stationary and the statement fails. Assuming each $Y_n$ measurable — which holds in every application — makes the pushforward identities available and the result true.
--
--   This is the bookkeeping step that lets the functional process $\{f(X_n)\}$ of a stationary Markov chain be fed into the central limit theorems of the mission, which are stated for general strictly stationary sequences.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4 (arXiv v2 p. 10): the functional process {f(X_n)} of a stationary chain is used as a stationary sequence in Theorems 5-8.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.isStrictlyStationary_comp_of_measurable {Ω X E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
    (P : Measure Ω) (Y : ℕ → Ω → X) (hY : ∀ n, Measurable (Y n))
    (hstat : IsStrictlyStationary P Y) (g : X → E) (hg : Measurable g) :
    IsStrictlyStationary P (fun i ω => g (Y i ω)) := by sorry
