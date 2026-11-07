-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_2_2
-- name    : Z2PostSamp.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:51.167216+00:00
-- url     : https://prove2.me/theorems/85fc5bd0-cbeb-4017-80a8-6a8d8b71ea16
-- title:
--   Lemma 2.2 — a polynomial-time logit program with the accuracy bounds (2.7) and the pathwise estimate along the target path
-- statement:
--   Fix $\lambda>1$. There are a deterministic program $\mathcal A^{\mathrm{vec}}$ of the log-cost RAM with dyadic real oracle, an exponent $c$, a constant $C$ and events $G_k\in\mathcal H_k=\sigma(J,(I_a,\theta_{I_a})_{a\le k})$ with $b_n:=\mathbb P(\cup_{k=k_0}^{n-1}G_k^c)\to0$ such that the following holds for every $n\ge2$.
--
--   1. For every $k_0\le k<n$, every real $n\times n$ matrix $J$, order $I$ and prefix, the program, with oracle $(J,\lambda)$ and input $n$, $k$ and the exposed pairs $(I_a,x_{I_a})_{1\le a\le k}$, halts with cost at most $c\,n^c$ and outputs a dyadic vector $\widehat\ell^{(k)}(x_{S_k})$.
--   2. Uniformly for $k_0\le k<n$,
--
--   $$\mathbb E\Big[\mathbf 1_{G_k}\big\|\widehat\ell^{(k)}(\theta_{S_k})-\ell^{(k)}(\theta_{S_k})\big\|^2\Big]\le\frac{C(n-k)}n,\qquad\mathbb E\Big[\mathbf 1_{G_k}\big|\widehat\ell^{(k)}_{I_{k+1}}(\theta_{S_k})-\ell^{(k)}_{I_{k+1}}(\theta_{S_k})\big|^2\Big]\le\frac Cn.\tag{2.7}$$
--
--   3. The simultaneous pathwise estimate holds:
--
--   $$\mathbb E_{J,I}\mu_J\Big(\sum_{k=k_0}^{n-1}\frac{\|\widehat\ell^{(k)}(\theta_{S_k})-\ell^{(k)}(\theta_{S_k})\|^2}{n-k}>\log n\Big)\le b_n+\frac C{\log n}.$$
--
--   The algorithmic vector and the exact vector are evaluated at the same posterior-distributed prefix; expectations include $J$, the independent order $I$ and $\theta\sim\mu_J$. This is the accuracy input of Lemma 2.3.
--
--   **Formalization Note** The program is chosen after $\lambda$ and before $n$, and it is run on the all-false coin tape, so it is deterministic. It sees only the exposed pairs of the order and the configuration. The vector $\widehat\ell^{(k)}$ is the implemented value that the program outputs. Norms are over $R_k$; expectations are lower Lebesgue integrals under the planted law.
--
--   Differences from the source:
--   - reading: an algorithm 𝒜vec computing ℓ̂^{(k)}(x_{S_k}) from J, λ and the exposed pairs in time n^{O_λ(1)} → one deterministic program of the log-cost RAM (run on the all-false tape), chosen after λ, with oracle (J, λ), input [n, k, I_1, x_{I_1}, …, I_k, x_{I_k}], dyadic output list, cost ≤ c·n^c; reason: the computational convention of §2 (p.6); the routine is deterministic (§3.3, App. B) because the replay of p.37 must reproduce it; the paper names no machine
--   - generalization: the running time on the algorithm's inputs → the cost bound for every real n × n matrix J, every order and prefix, for k₀ ≤ k < n; reason: a bound on every input implies the bound on the model's inputs; the caps of App. B.3 give it
--   - reading: k₀ ≤ k < n with k₀ of (2.3); App. B.2's implemented prefix length may be k₀ + 1 (p.39) → the range k₀ ≤ k < n with the exact value (2.3); reason: the stronger of the two readings; at the one extra index the orientation (2.13) uses the k₀ coordinates that are exposed, and the analysis of §3 applies to that length too
--   - reading: θ ∼ μ_J, expectations including J and the independent order I → integrals under the planted law of (θ, Z, I); reason: §2 preamble, p.5; Lemma 3.1 identifies the two
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 2.2, p.8, (2.7); §2 preamble, p.6; §3.3, p.25; App. B, pp.38–41

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_Machine
import Definitions.Def_Z2PostSamp_SamplerIO

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 2.2 (logit accuracy along the target path).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 2.2, p.8: "Fix `λ > 1`. For `n ≥ 2` and every `k₀ ≤ k < n`, there exists an algorithm
`𝒜^vec` that computes a vector `ℓ̂^{(k)}(x_{S_k})` from `J, λ` and the exposed pairs
`(I_a, x_{I_a})_{1≤a≤k}` in time `n^{O_λ(1)}` with the following properties. For `θ ∼ μ_J`, let
`ℋ_k = σ(J, (I_a, θ_{I_a})_{a≤k})`. There are events `G_k ∈ ℋ_k` and a constant `C = C_λ < ∞` such that
`b_n := P(∪_{k=k₀}^{n−1} G_kᶜ) = o(1)` and, uniformly for `k₀ ≤ k < n`,
`E[1_{G_k} ‖ℓ̂^{(k)}(θ_{S_k}) − ℓ^{(k)}(θ_{S_k})‖²] ≤ C(n − k)/n`,
`E[1_{G_k} |ℓ̂^{(k)}_{I_{k+1}}(θ_{S_k}) − ℓ^{(k)}_{I_{k+1}}(θ_{S_k})|²] ≤ C/n` (2.7). … In particular, we have
the simultaneous pathwise estimate
`E_{J,I} μ_J(Σ_{k=k₀}^{n−1} ‖ℓ̂^{(k)}(θ_{S_k}) − ℓ^{(k)}(θ_{S_k})‖²/(n − k) > log n) ≤ b_n + C/log n = o(1)`."

**Formalization Note.** `𝒜^vec` is one deterministic program `P` of the log-cost RAM with dyadic real
oracle (run on the all-`false` tape), chosen after `λ` and before `n`. Its input is the list
`[n, k]` followed by the exposed pairs only, its oracle holds `J` and `λ`, and its output is a dyadic
vector (`algoLogit`), so `ℓ̂^{(k)}` is the implemented value, not an exact-arithmetic target. "In time
`n^{O_λ(1)}`" is the cost bound `c·nᶜ` for every real matrix `J`, order and prefix. `k₀` is the exact
value (2.3); App. B.2 implements a value that may be larger by one (p.39), and a program whose orientation
uses the prefix it has serves the extra index. Norms are over `R_k`, where `ℓ^{(k)}` lives. Expectations
are lower Lebesgue integrals under the planted law of `(θ, Z, I)` (§2 preamble, p.5). -/
theorem lemma_2_2 (lam : ℝ) (hlam : 1 < lam) :
    ∃ (P : Program) (c : ℕ) (C : ℝ) (G : (n : ℕ) → ℕ → Set (PΩ n)),
      (∀ n k, MeasurableSet[Hk n lam k] (G n k)) ∧
      Tendsto (fun n => plantedLaw n (⋃ k ∈ Finset.Ico (k0 n lam) n, (G n k)ᶜ)) atTop (𝓝 0) ∧
      ∀ n : ℕ, 2 ≤ n →
        (∀ k, k0 n lam ≤ k → k < n → ∀ (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n))
          (x : Spin n), HaltsWithin P (oracleOf n J lam) (prefixInput I x k) zeroTape (c * n ^ c)) ∧
        (∀ k (hk : k < n), k0 n lam ≤ k →
          ∫⁻ ω, (G n k).indicator (fun ω => ENNReal.ofReal (∑ i ∈ Rset ω.2.2 k,
              (algoLogit P n lam (c * n ^ c) (Jof n lam ω) ω.2.2 ω.1 k i -
                logit (Jof n lam ω) ω.2.2 ω.1 k i) ^ 2)) ω
            ∂(plantedLaw n) ≤ ENNReal.ofReal (C * ((n : ℝ) - k) / n) ∧
          ∫⁻ ω, (G n k).indicator (fun ω => ENNReal.ofReal
              ((algoLogit P n lam (c * n ^ c) (Jof n lam ω) ω.2.2 ω.1 k (ω.2.2 ⟨k, hk⟩) -
                logit (Jof n lam ω) ω.2.2 ω.1 k (ω.2.2 ⟨k, hk⟩)) ^ 2)) ω
            ∂(plantedLaw n) ≤ ENNReal.ofReal (C / n)) ∧
        plantedLaw n {ω | Real.log n < ∑ k ∈ Finset.Ico (k0 n lam) n,
            (∑ i ∈ Rset ω.2.2 k,
              (algoLogit P n lam (c * n ^ c) (Jof n lam ω) ω.2.2 ω.1 k i -
                logit (Jof n lam ω) ω.2.2 ω.1 k i) ^ 2) /
            ((n : ℝ) - k)}
          ≤ plantedLaw n (⋃ k ∈ Finset.Ico (k0 n lam) n, (G n k)ᶜ) +
            ENNReal.ofReal (C / Real.log n) := by sorry

end Z2PostSamp
