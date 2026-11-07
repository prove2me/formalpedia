-- Prove2me | Theorems.Thm_Z2PostSamp_eq_3_8
-- name    : Z2PostSamp.eq_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:55.716203+00:00
-- url     : https://prove2.me/theorems/b0c66d32-eb1c-4099-8bd6-5f4ec7461aca
-- title:
--   (3.8) — the maximal estimate $\max_{p\le k\le h}\|\bar m^{(k)}-w\|^2/n\le d-c+o_{\mathbb P}(1)$
-- statement:
--   Fix $\lambda>1$. Let $p=p_n\le h=h_n\le n$ be deterministic indices and let $w\in[-1,1]^n$ be $\mathcal H_p$-measurable. Suppose, for deterministic constants $c,d$, that
--
--   $$\frac{\|w\|^2}n\xrightarrow{L^2}c,\qquad\frac{\langle\theta,w\rangle}n\xrightarrow{L^2}c,\qquad\frac{\|\bar m^{(h)}(\theta_{S_h})\|^2}n\xrightarrow{L^2}d .$$
--
--   Then
--
--   $$\max_{p\le k\le h}\frac{\|\bar m^{(k)}(\theta_{S_k})-w\|^2}n\le d-c+o_{\mathbb P}(1).$$
--
--   Here $\bar m^{(k)}$ is the posterior mean of $\theta$ given $\mathcal H_k$ (the conditional mean extended by the revealed signs), and all probabilities are under the planted law. The estimate transfers convergence at deterministic checkpoints to every time of the revealing path without a union bound; it is the main tool in the proof of Lemma 2.4.
--
--   **Formalization Note** $L^2$ convergence is $\mathbb E|X_n-c|^2\to0$ (lower Lebesgue integral). "$\le d-c+o_{\mathbb P}(1)$" is: for every $\varepsilon>0$ the probability that some $k\in[p_n,h_n]$ has $\|\bar m^{(k)}-w\|^2/n>d-c+\varepsilon$ tends to $0$.
--
--   Differences from the source:
--   - encoding: max_{p≤k≤h} X_k ≤ d − c + o_P(1) → ∀ ε > 0, P(∃ k ∈ [p_n, h_n], X_k > d − c + ε) → 0; reason: definition of o_P(1) for a maximum
--   - encoding: →^{L²} → E|X_n − c|² → 0 as a lower Lebesgue integral; reason: the integrands are nonnegative
--   - reading: deterministic indices p ≤ h → p_n ≤ h_n ≤ n; reason: the indices are times of the revealing path, which has n steps
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §3.2, p.19, (3.8); p.18 (m̄^{(k)})

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_Construction

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **(3.8): the maximal estimate along the revealing path.**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §3.2, p.19: "Let `p = p_n ≤ h = h_n` be deterministic indices and let `w ∈ [−1,1]ⁿ` be
`ℋ_p`-measurable. Suppose, for deterministic constants `c, d`, that `‖w‖²/n →^{L²} c`,
`⟨θ, w⟩/n →^{L²} c`, `‖m̄^{(h)}(θ_{S_h})‖²/n →^{L²} d`. Then
`max_{p≤k≤h} ‖m̄^{(k)}(θ_{S_k}) − w‖²/n ≤ d − c + o_P(1)` (3.8)." Here `m̄^{(k)}` is the conditional
mean extended by `x_i` on `S_k` (p.18), and probabilities are under the planted law (p.18).

**Formalization Note.** `p_n ≤ h_n ≤ n` (the indices are revealing times). `w_n` is a function on
the planted sample space with values in `[−1,1]ⁿ`, measurable for `ℋ_{p_n}`. `→^{L²}` is
`E|X_n − c|² → 0` (lower Lebesgue integral), and `≤ d − c + o_P(1)` is: for every `ε > 0` the
planted probability that some `k ∈ [p_n, h_n]` has `‖m̄^{(k)} − w_n‖²/n > d − c + ε` tends to `0`. -/
theorem eq_3_8 (lam : ℝ) (hlam : 1 < lam) (p h : ℕ → ℕ) (hph : ∀ n, p n ≤ h n)
    (hhn : ∀ n, h n ≤ n) (w : (n : ℕ) → PΩ n → Fin n → ℝ) (hw1 : ∀ n ω i, |w n ω i| ≤ 1)
    (hwm : ∀ n, Measurable[Hk n lam (p n)] (w n)) (c d : ℝ)
    (hc1 : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal ((sqNorm (w n ω) / n - c) ^ 2)
      ∂(plantedLaw n)) atTop (𝓝 0))
    (hc2 : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (((spinVec ω.1 ⬝ᵥ w n ω) / n - c) ^ 2)
      ∂(plantedLaw n)) atTop (𝓝 0))
    (hd : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal
      ((sqNorm (condMean (Jof n lam ω) ω.2.2 ω.1 (h n)) / n - d) ^ 2) ∂(plantedLaw n))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => plantedLaw n {ω | ∃ k, p n ≤ k ∧ k ≤ h n ∧
        d - c + ε < sqNorm (condMean (Jof n lam ω) ω.2.2 ω.1 k - w n ω) / n}) atTop (𝓝 0) := by sorry

end Z2PostSamp
