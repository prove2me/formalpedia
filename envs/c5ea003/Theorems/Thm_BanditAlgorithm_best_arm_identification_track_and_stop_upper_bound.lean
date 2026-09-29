-- Prove2me | Theorems.Thm_BanditAlgorithm_best_arm_identification_track_and_stop_upper_bound
-- name    : BanditAlgorithm.best_arm_identification_track_and_stop_upper_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T18:09:55.627813+00:00
-- url     : https://prove2.me/theorems/d2f1c7d6-0e58-4864-9356-200fe7d080aa
-- title:
--   Track-and-Stop upper bound: $\\limsup_{\\delta\\to0}\\mathbb{E}[\\tau_\\delta]/\\log(1/\\delta)\\le c^*(\\nu)$
-- statement:
--   (Track-and-Stop, upper half of Theorem 33.6) Over the class $\mathcal{E}=\mathcal{E}^k_{\mathcal{N}}(1)$ of unit-variance Gaussian bandits there exist a policy $\pi$ (not depending on $\delta$) and, for each confidence level $\delta\in(0,1)$, a stopping time $\tau_\delta$ of the natural filtration together with an $\mathcal{F}_{\tau_\delta}$-measurable recommendation rule $\psi_\delta$, such that:
--
--   1. **Soundness.** Each triple $(\pi,\tau_\delta,\psi_\delta)$ is $\delta$-sound for $\mathcal{E}$.
--   2. **Finiteness.** For every $\nu\in\mathcal{E}$ with a unique optimal arm and every $\delta\in(0,1)$, the expected stopping time $\mathbb{E}_{\nu\pi}[\tau_\delta]$ is finite.
--   3. **Asymptotic upper bound.** For every such $\nu$ and every $\varepsilon>0$, eventually as $\delta\to 0^+$,
--   $$\frac{\mathbb{E}_{\nu\pi}[\tau_\delta]}{\log(1/\delta)} \;\le\; c^*(\nu)+\varepsilon .$$
--
--   Clause 3 is the statement $\limsup_{\delta\to 0^+}\mathbb{E}_{\nu\pi}[\tau_\delta]/\log(1/\delta)\le c^*(\nu)$, written in its $\varepsilon$-form so that it is free of the junk values a real-valued `limsup` takes on a function that is not bounded above.
--
--   This is the **upper** half of L&S Theorem 33.6; the matching lower half is Theorem 33.5, on the platform as `BanditAlgorithm.best_arm_identification_sample_complexity_lower_bound`. Together the two halves give the limit asserted by Theorem 33.6, and the reduction performing that squeeze is already accepted against the root.
--
--   **Where the three clauses come from, and a constant that must be watched.**
--
--   L&S only *sketch* Theorem 33.6 (p. 410: "we sketch the proof ... a more complete outline is given in Exercise 33.6"), so the pieces have to be assembled from two places.
--
--   *Clause 1 (soundness) is L&S Lemma 33.7*, which is specific to Gaussian bandits: with $f(x)=e^{k-x}(x/k)^k$ on $[k,\infty)$ and the threshold
--   $$\beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta),$$
--   the Chernoff stopping rule $\tau=\min\{t: Z_t\ge\beta_t(\delta)\}$ satisfies $\mathbb{P}(i^*(\hat\nu(\tau))\ne i^*(\nu))\le\delta$ — **exactly, at every $\delta$**, with no inflation of the leading constant, because $f^{-1}(\delta)=(1+o(1))\log(1/\delta)$.
--
--   This is the reason clause 1 and clause 3 can hold *simultaneously with the constant $c^*(\nu)$ itself*. It is worth being explicit that the analogous general-exponential-family result of Garivier & Kaufmann (COLT 2016), their Proposition 12, does **not** suffice here: it requires $\alpha>1$ in the threshold $\beta(t,\delta)=\log(Ct^\alpha/\delta)$, and combining it with their Theorem 14 yields only $\limsup \le \alpha T^*(\mu)$ for $\alpha>1$ — as they themselves summarise ("combining Proposition 12 and Theorem 14, one obtains for every $\alpha>1$ ..."). Anyone attacking this node through the general exponential-family route will land on $\alpha T^*$ and miss the statement; the Gaussian threshold of Lemma 33.7 is what closes the gap.
--
--   *Clauses 2 and 3* are the content of Garivier & Kaufmann's **Proposition 13** (almost-sure finiteness and integrability of $\tau_\delta$ — a separate result, not a corollary of the expectation bound, which is why finiteness is carried here as its own clause: without it the `ENNReal.toReal` in the root would silently read $\infty$ as $0$) and **Theorem 14** (the $\limsup$ bound). Their dependencies: forced-exploration concentration (Lemma 19), the tracking lemmas (7 and 8), and a Lambert-$W$ estimate (Lemma 18). None of these exist in Mathlib.
--
--   A bookkeeping caveat for the $\limsup$: Theorem 14 is stated for $\beta(t,\delta)=\log(r(t)/\delta)$ with $r(t)=O(t^\alpha)$, $\alpha\in[1,e/2]$, and gives $\alpha T^*(\mu)$, whereas L&S's threshold has $r(t)=(t^2+t)^k$, i.e. $\alpha=2k$. The $\alpha$ in Theorem 14 is an artefact of the explicit (deliberately lossy) solution of $c_1x\ge\log(c_2x^\alpha)$ supplied by their Lemma 18: the *least* such $x$ is $\sim(\log c_2)/c_1$, not $\sim(\alpha\log c_2)/c_1$. Since $c_2\propto 1/\delta$ and the polynomial factor contributes only $O(\log\log(1/\delta))$, the true asymptotics are $\tau_\delta\sim c^*(\nu)\log(1/\delta)$ for any polynomial $r$ — which is exactly what L&S's proof sketch asserts. A formal proof should therefore redo the Lemma 18 step without the $\alpha$ inflation rather than cite Theorem 14 verbatim.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 33.6 p. 410 (upper half) with Lemma 33.7 p. 409 supplying the Gaussian threshold beta_t(delta) = k log(t^2+t) + f^{-1}(delta) that is sound at every delta; the complete expectation analysis is Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016 (PMLR v49), arXiv:1602.04589, Proposition 13 (finiteness) and Theorem 14 (limsup). NOTE: G&K Proposition 12 is NOT usable for clause 1 - it requires alpha > 1 and yields only limsup <= alpha T*(mu); the exact constant comes from L&S Lemma 33.7.

import Definitions.Def_BanditTrajectory
import Definitions.Def_GaussianBandit


open MeasureTheory ProbabilityTheory Filter ENNReal

theorem BanditAlgorithm.best_arm_identification_track_and_stop_upper_bound {k : ℕ}
    (hk : 0 < k) :
    ∃ (π : BanditPolicy k) (τ : ℝ → (ℕ → Fin k × ℝ) → ℕ∞)
      (ψ : ℝ → (ℕ → Fin k × ℝ) → Fin k),
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        ∃ hτ : IsBanditStoppingTime (τ δ),
          Measurable[hτ.measurableSpace] (ψ δ) ∧
            IsSoundBAI δ π (τ δ) (ψ δ) (Set.range (gaussianBandit (k := k)))) ∧
      ∀ ν ∈ Set.range (gaussianBandit (k := k)), (∃! i, i ∈ banditOptimalArms ν) →
        (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
            ∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂banditTrajMeasure ν π ≠ ⊤) ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂banditTrajMeasure ν π).toReal / Real.log (1 / δ)
                ≤ (baiComplexity ν (Set.range (gaussianBandit (k := k)))).toReal + ε := by
  sorry
