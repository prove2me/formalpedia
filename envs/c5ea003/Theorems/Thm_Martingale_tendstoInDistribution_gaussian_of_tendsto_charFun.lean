-- Prove2me | Theorems.Thm_Martingale_tendstoInDistribution_gaussian_of_tendsto_charFun
-- name    : Martingale.tendstoInDistribution_gaussian_of_tendsto_charFun
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:38:39.07819+00:00
-- url     : https://prove2.me/theorems/561dc074-7061-4ed7-b3e3-0f37fc95ddf2
-- title:
--   Lévy continuity in CLT form: pointwise convergence of $\mathbb{E}[e^{itX_n}]$ to $e^{-vt^2/2}$ gives $X_n \Rightarrow \mathcal{N}(0,v)$
-- statement:
--   Let $(X_n)_{n\in\mathbb{N}}$ be measurable real random variables on a probability space $(\Omega,\mathcal{F},\mathbb{P})$, and let $v \ge 0$. If for every $t \in \mathbb{R}$
--
--   $$\mathbb{E}\bigl[e^{i t X_n}\bigr] \;\longrightarrow\; e^{-v t^{2}/2},$$
--
--   then $X_n$ converges in distribution to $\mathcal{N}(0, v)$.
--
--   **What it is for.** This is the packaging of Lévy's continuity theorem in the exact form that central limit arguments produce their output. A CLT proof — whether for independent summands, martingale differences, or mixing sequences — invariably ends with a pointwise statement about characteristic functions: for each fixed $t$, the expectation $\mathbb{E}[e^{itX_n}]$ converges to the Gaussian characteristic function. The conclusion that is actually wanted, weak convergence of the laws, then requires (i) recognising $\mathbb{E}[e^{itX_n}]$ as the characteristic function of the pushforward law $\mathbb{P}\circ X_n^{-1}$, (ii) computing the characteristic function of $\mathcal{N}(0,v)$, and (iii) invoking Lévy continuity. This statement performs all three once, so that a CLT proof can stop at the characteristic-function estimate.
--
--   **On the degenerate case.** No positivity of $v$ is assumed beyond $v \ge 0$: for $v = 0$ the conclusion is convergence in distribution to the Dirac mass at $0$, which is the correct degenerate statement and is exactly what is needed when a CLT is applied to a functional of asymptotic variance zero. Formally this is handled by the coercion $v \mapsto v_+$ into $\mathbb{R}_{\ge 0}$, which is the identity precisely because $v \ge 0$.
--
--   **Proof.** The pushforward $\mathbb{P}\circ X_n^{-1}$ is a probability measure since $X_n$ is measurable, and by the change-of-variables formula its characteristic function at $t$ is
--   $$\int e^{i t x}\,\mathrm{d}(\mathbb{P}\circ X_n^{-1})(x) \;=\; \int e^{i t X_n(\omega)}\,\mathrm{d}\mathbb{P}(\omega) \;=\; \mathbb{E}\bigl[e^{itX_n}\bigr].$$
--   The characteristic function of $\mathcal{N}(\mu, v)$ is $t \mapsto e^{it\mu - vt^2/2}$, which at $\mu = 0$ is the assumed limit. Lévy's continuity theorem — pointwise convergence of characteristic functions to the characteristic function of a probability measure implies weak convergence — then gives convergence of the laws, which is the definition of convergence in distribution.
-- source:
--   P. Lévy, Calcul des Probabilités, Gauthier-Villars 1925 (continuity theorem); P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Theorem 26.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Section 3.2.

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem Martingale.tendstoInDistribution_gaussian_of_tendsto_charFun
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (v : ℝ) (hv : 0 ≤ v)
    (h : ∀ t : ℝ, Tendsto (fun n : ℕ => ∫ ω, Complex.exp (Complex.I * t * (X n ω : ℂ)) ∂P) atTop
        (𝓝 (Complex.exp (-(v * t ^ 2) / 2)))) :
    TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 v.toNNReal) := by sorry
