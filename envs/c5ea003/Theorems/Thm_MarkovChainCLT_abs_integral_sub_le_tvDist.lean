-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist
-- name    : MarkovChainCLT.abs_integral_sub_le_tvDist
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T20:48:01.94049+00:00
-- url     : https://prove2.me/theorems/809417df-59bb-4e3f-b56d-86ffb0817287
-- title:
--   Total variation bounds differences of integrals of $[0,1]$-valued functions
-- statement:
--   Let $\mu, \nu$ be finite measures on a measurable space $\mathsf{X}$ and let $f : \mathsf{X} \to \mathbb{R}$ be measurable with $0 \le f \le 1$ everywhere. Then
--
--   $$\left| \int f \,\mathrm{d}\mu - \int f \,\mathrm{d}\nu \right| \;\le\; \|\mu - \nu\| \;:=\; \sup_{A \text{ measurable}} \bigl|\mu(A) - \nu(A)\bigr|.$$
--
--   **What it upgrades.** The total variation distance is *defined* as a supremum over measurable **sets** — equivalently, over indicator functions. This theorem says the same bound holds for every measurable **function** with values in $[0,1]$. The set version is the special case $f = \mathbf{1}_A$; the function version is what is actually needed, and it does not follow formally from the definition.
--
--   **Why it is indispensable for Markov chains.** Every quantitative mixing estimate has the same shape: one has a rate $\|P^n(x,\cdot) - \pi\| \le C$ and wants to conclude that some functional of the chain started at $x$ differs from the same functional under stationarity by at most $C$. The functional in question is almost never an indicator of a set in $\mathsf{X}$ — it is $x \mapsto K(x, B)$ for a kernel $K$ and a set $B$ in a *different* space, typically path space. Concretely, for a Markov kernel $K$ and measurable $B$,
--   $$\bigl|(K \circ \mu)(B) - (K \circ \nu)(B)\bigr| = \left|\int K(x,B)\,\mathrm{d}\mu(x) - \int K(x,B)\,\mathrm{d}\nu(x)\right| \;\le\; \|\mu - \nu\|,$$
--   since $x \mapsto K(x,B)$ takes values in $[0,1]$. That is the data-processing inequality: *applying a Markov kernel cannot increase total variation distance*. It is the step that transports a rate of convergence on the state space to a bound on path-space events, and hence the step that turns an ergodicity hypothesis into a mixing-coefficient bound.
--
--   **Proof.** The definition of $\|\mu-\nu\|$ as a supremum over sets gives no direct handle on integrals; the bridge is the unsigned Hahn decomposition. Choose a measurable $s$ with $\nu \le \mu$ on subsets of $s$ and $\mu \le \nu$ on subsets of $s^{c}$; equivalently, as measures, $\nu|_s \le \mu|_s$ and $\mu|_{s^c} \le \nu|_{s^c}$. Split each integral over $s$ and $s^c$. On $s^c$ the difference $\int_{s^c} f\,\mathrm{d}\mu - \int_{s^c} f\,\mathrm{d}\nu$ is $\le 0$ because $f \ge 0$ and $\mu \le \nu$ there. On $s$, applying the same monotonicity to $1 - f \ge 0$ gives
--   $$\int_s (1-f)\,\mathrm{d}\nu \;\le\; \int_s (1-f)\,\mathrm{d}\mu, \qquad\text{i.e.}\qquad \int_s f\,\mathrm{d}\mu - \int_s f\,\mathrm{d}\nu \;\le\; \mu(s) - \nu(s).$$
--   Adding the two gives $\int f\,\mathrm{d}\mu - \int f\,\mathrm{d}\nu \le \mu(s) - \nu(s) \le \|\mu-\nu\|$. The reverse inequality is the same argument with the roles of $\mu$ and $\nu$ exchanged and $s$ replaced by $s^c$. Note the two applications of "$1-f$ rather than $f$" are what make the bound $\mu(s)-\nu(s)$ appear rather than the useless $\int_s f \,\mathrm{d}\mu$.
-- source:
--   H. Hahn, "Über die Integrale des Herrn Hellinger und die Orthogonalinvarianten der quadratischen Formen von unendlich vielen Veränderlichen", Monatsh. Math. Phys. 23 (1912) 161-224; D. A. Levin and Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Proposition 4.5 and Lemma 4.11; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16.

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open MarkovChainCLT

theorem MarkovChainCLT.abs_integral_sub_le_tvDist {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ tvDist μ ν := by sorry
