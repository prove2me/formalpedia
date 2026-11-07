-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_2_3
-- name    : Z2PostSamp.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:35.873666+00:00
-- url     : https://prove2.me/theorems/610dfb1e-afd7-4ec5-953f-c8c87e458f0d
-- title:
--   Lemma 2.3 — the sequential proposal is a positive probability, admits polynomial-time sampling and log-density evaluation, and is warm: $\mathbb E\,\mu_J(d\mu_J/dQ>2^{k_0}e^u)\le b_n+(C+1/e)/u$
-- statement:
--   **Computation.** Fix $\lambda>1$ and let $\mathcal A^{\mathrm{vec}}$ be any deterministic logit program with cost at most $c\,n^c$ on the inputs of Lemma 2.2, for $k_0(n,\lambda)\le k<n$. Then there are two programs, a sampler and an evaluator, such that for every accuracy exponent $K$ there is $c'$ with the following property for all $n\ge2$, all $k_0$ between the value (2.3) and $n$, every real matrix $J$ and order $I$, with $Q$ the proposal (2.6) built from the logits of $\mathcal A^{\mathrm{vec}}$:
--
--   1. on input $(K,n,k_0,I)$ and every coin tape the sampler halts with cost at most $c'n^{c'}$, and its output law is within $n^{-K}$ of $Q$ in total variation;
--   2. on input $(K,n,k_0,I,x)$ the evaluator is deterministic, halts with cost at most $c'n^{c'}$, and outputs a dyadic number within $n^{-K}$ of $\log Q(x)$.
--
--   **Warmness.** Fix $\lambda>1$, $n\ge2$ and $k_0\le n$. For every data matrix $J$ and order $I$ let logit maps $\widehat\ell^{(k)}$, $k_0\le k<n$, be given, each depending on a configuration only through its prefix $x_{S_k}$, and let $Q=Q_{J,I}$ be the sequential proposal (2.6). Let $G_k\in\mathcal H_k$ be events and $C\ge0$ a constant with
--
--   $$\mathbb E\Big[\mathbf 1_{G_k}\big|\widehat\ell^{(k)}_{I_{k+1}}(\theta_{S_k})-\ell^{(k)}_{I_{k+1}}(\theta_{S_k})\big|^2\Big]\le\frac Cn,\qquad k_0\le k<n,$$
--
--   the second bound of (2.7), where the expectation is over the planted law of $(\theta,Z,I)$ (so $\theta\sim\mu_J$ given $J$), and put $b_n=\mathbb P\big(\cup_{k=k_0}^{n-1}G_k^c\big)$. Then:
--
--   1. $Q$ is strictly positive and sums to one;
--   2. for every $u>0$,
--   $$\mathbb E_{J,I}\,\mu_J\Big(\frac{d\mu_J}{dQ}>2^{k_0}e^u\Big)\le b_n+\frac{C+1/e}u ;\tag{2.8}$$
--   3. with $M=2^{k_0}n$ and $\delta=\mu_J(d\mu_J/dQ>M)$, $\ \mathbb E_{J,I}\,\delta\le b_n+\frac{C+1/e}{\log n}$.
--
--   With Lemma 2.2 ($b_n=o(1)$) and $k_0$ of (2.3), the last bound is $o(1)$ and $M=n^{O_\lambda(1)}$, so Lemma 2.1 applies with a polynomial number of correction steps.
--
--   **Formalization Note** The computational part follows the convention of p.6 (log-density to a prescribed inverse-polynomial absolute accuracy) and App. B.5 (draws made from fair bits to prescribed accuracy): exact draws from $Q$ are not possible on fair bits with bounded cost, and the paper's own implementation is approximate. The warmness part is stated for any prefix-function logit maps (measurable along the planted path), any $k_0\le n$, any $G_k\in\mathcal H_k$ and $C\ge0$ meeting the displayed bound: the proof uses only these properties, and the paper's proposal, its $k_0$, $G_k$ and $C$ are an instance. Expectations are lower Lebesgue integrals.
--
--   Differences from the source:
--   - generalization: the proposal of Algorithm 3 (logits ℓ̂ of Lemma 2.2), k₀ of (2.3), the events G_k and constant C of Lemma 2.2 → warmness for any prefix-function logit maps measurable along the planted path, any k₀ ≤ n, any G_k ∈ ℋ_k and C ≥ 0 satisfying the second bound of (2.7); reason: the proof uses only prefix measurability and that bound; the paper's objects satisfy the hypotheses
--   - generalization: Q admits polynomial-time sampling and log-density evaluation, for the logits of Lemma 2.2 → sampler and evaluator programs for the proposal of any deterministic logit program with cost ≤ c·n^c, with cost ≤ c'·n^{c'} on every real J, order, tape and configuration; reason: Lemma 2.2's program is one such logit program; a bound on every input implies the bound on the model's inputs
--   - reading: polynomial-time sampling and log-density evaluation in the computational convention above → for every K, output law within n^{−K} of Q in total variation, drawn on fair bits, and log Q(x) within n^{−K}; K is an input of the two programs; reason: p.6: log-density 'to a prescribed inverse-polynomial absolute accuracy'; App. B.5: finite-bit draws to prescribed accuracy; p.6 reserves exact draws for the ideal law
--   - reading: k₀ of (2.3), computed by the sampler → k₀ supplied on the program's input, any value from (2.3) up to n; reason: p.36 treats k₀ as known and App. B.2 implements a certified value instead of deciding the ceiling at an integer boundary; the input covers both values
--   - reading: E_{J,I} μ_J(·) and θ ∼ μ_J → integrals under the planted law of (θ, Z, I); reason: §2 preamble, p.5: expectations in the analysis are under the joint planted law
--   - encoding: n (Lemma 2.2's standing n ≥ 2) → hypothesis 2 ≤ n; reason: log n > 0 in the last bound; the lemma is stated in the setting of Lemma 2.2
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 2.3, p.9, (2.8); (2.6), p.8; Lemma 2.2's (2.7), p.8; §2 preamble, p.6; App. B.5, pp.40–41

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_Machine
import Definitions.Def_Z2PostSamp_SamplerIO
import Definitions.Def_Z2PostSamp_Proposal
import Definitions.Def_Z2PostSamp_IndepMetropolis

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 2.3 (warmness of the sequential proposal), generalized.**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 2.3, p.9: "The proposal `Q` in (2.6) is strictly positive, admits polynomial-time
sampling and log-density evaluation in the computational convention above. In addition, for every
`u > 0`, `E_{J,I} μ_J(dμ_J/dQ > 2^{k₀} e^u) ≤ b_n + (C + 1/e)/u` (2.8). Consequently, it is
`(δ, M)`-warm with respect to `μ_J`, where `M = 2^{k₀} n = n^{O_λ(1)}`, `δ = μ_J(dμ_J/dQ > M)`,
`E_{J,I} δ ≤ b_n + (C + 1/e)/log n = o(1)`." Here `b_n = P(∪_{k=k₀}^{n−1} G_kᶜ)` and `C` are those of
Lemma 2.2, p.8, whose second bound (2.7) is
`E[1_{G_k} |ℓ̂^{(k)}_{I_{k+1}}(θ_{S_k}) − ℓ^{(k)}_{I_{k+1}}(θ_{S_k})|²] ≤ C/n`.

**Formalization Note.** The first conjunct is the computational clause, in the convention of p.6
("computing the log-density to a prescribed inverse-polynomial absolute accuracy"; App. B.5 for the
draws): for **any** deterministic logit program `Pv` with cost `≤ c·nᶜ` (Lemma 2.2's is one) there are
one sampling and one evaluation program that, given `K`, approximate the law `Q` of (2.6) to total
variation `n^{−K}` on fair bits and evaluate `log Q(x)` to absolute error `n^{−K}`, with cost `≤ c'·n^{c'}`
on every matrix, order, tape and configuration. `k₀` is supplied on the input (p.36: "the known `k₀`"),
as the value (2.3) or the value of App. B.2. The remaining conjuncts are stated for **any** logit maps
`lh k` (for fixed `J, I`, prefix functions of `x`, jointly measurable along the planted path), any
`k₀ ≤ n`, any events `G_k ∈ ℋ_k` and any `C ≥ 0` satisfying the second bound of (2.7); the proof uses
nothing else about the algorithm, so this specializes to the paper's `ℓ̂`, `k₀` of (2.3), `G_k`, `C`. The
expectation `E_{J,I}` and `θ ∼ μ_J` are the planted law of `(θ, Z, I)` (§2 preamble, p.5).
`μ_J(dμ_J/dQ > s)` is `warmDelta μ_J Q s`. -/
theorem lemma_2_3 :
    (∀ lam : ℝ, 1 < lam → ∀ (Pv : Program) (c : ℕ),
      (∀ n : ℕ, 2 ≤ n → ∀ k, k0 n lam ≤ k → k < n → ∀ (J : Matrix (Fin n) (Fin n) ℝ)
        (I : Equiv.Perm (Fin n)) (x : Spin n),
        HaltsWithin Pv (oracleOf n J lam) (prefixInput I x k) zeroTape (c * n ^ c)) →
      ∃ Ps Pe : Program, ∀ K : ℕ, ∃ c' : ℕ, ∀ n : ℕ, 2 ≤ n → ∀ k₀ : ℕ, k0 n lam ≤ k₀ → k₀ ≤ n →
        ∀ (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)),
        (∀ ω : ℕ → Bool, HaltsWithin Ps (oracleOf n J lam) (sampleInput K k₀ I) ω (c' * n ^ c')) ∧
        lawTV (tapeLaw Ps (oracleOf n J lam) (sampleInput K k₀ I) n (c' * n ^ c'))
            (propQ k₀ I fun k x => algoLogit Pv n lam (c * n ^ c) J I x k) ≤ ((n : ℝ) ^ K)⁻¹ ∧
        ∀ x : Spin n,
          HaltsWithin Pe (oracleOf n J lam) (evalInput K k₀ I x) zeroTape (c' * n ^ c') ∧
          |decodeDyadic (outputAt Pe (oracleOf n J lam) (evalInput K k₀ I x) zeroTape (c' * n ^ c')) 0
            - Real.log (propQ k₀ I (fun k y => algoLogit Pv n lam (c * n ^ c) J I y k) x)|
            ≤ ((n : ℝ) ^ K)⁻¹) ∧
    ∀ (lam : ℝ) (hlam : 1 < lam) (n : ℕ) (hn : 2 ≤ n) (k₀ : ℕ) (hk₀ : k₀ ≤ n)
    (lh : ℕ → Matrix (Fin n) (Fin n) ℝ → Equiv.Perm (Fin n) → Spin n → Fin n → ℝ)
    (hpre : ∀ k, k₀ ≤ k → k < n → ∀ J I, IsPrefixFn I k (lh k J I))
    (hmeas : ∀ k, k₀ ≤ k → k < n → Measurable fun ω : PΩ n => lh k (Jof n lam ω) ω.2.2 ω.1)
    (G : ℕ → Set (PΩ n)) (hG : ∀ k, MeasurableSet[Hk n lam k] (G k)) (C : ℝ) (hC : 0 ≤ C)
    (hacc : ∀ k (hk : k < n), k₀ ≤ k →
      ∫⁻ ω, (G k).indicator (fun ω => ENNReal.ofReal
          ((lh k (Jof n lam ω) ω.2.2 ω.1 (ω.2.2 ⟨k, hk⟩) -
            logit (Jof n lam ω) ω.2.2 ω.1 k (ω.2.2 ⟨k, hk⟩)) ^ 2)) ω ∂(plantedLaw n)
        ≤ ENNReal.ofReal (C / n)),
    (∀ J I x, 0 < propQ k₀ I (fun k => lh k J I) x) ∧
    (∀ J I, ∑ x, propQ k₀ I (fun k => lh k J I) x = 1) ∧
    (∀ u : ℝ, 0 < u →
      ∫⁻ ω, ENNReal.ofReal (warmDelta (isingLaw (Jof n lam ω))
          (propQ k₀ ω.2.2 (fun k => lh k (Jof n lam ω) ω.2.2)) ((2 : ℝ) ^ k₀ * Real.exp u))
        ∂(plantedLaw n)
        ≤ plantedLaw n (⋃ k ∈ Finset.Ico k₀ n, (G k)ᶜ) +
          ENNReal.ofReal ((C + 1 / Real.exp 1) / u)) ∧
    ∫⁻ ω, ENNReal.ofReal (warmDelta (isingLaw (Jof n lam ω))
        (propQ k₀ ω.2.2 (fun k => lh k (Jof n lam ω) ω.2.2)) ((2 : ℝ) ^ k₀ * n)) ∂(plantedLaw n)
      ≤ plantedLaw n (⋃ k ∈ Finset.Ico k₀ n, (G k)ᶜ) +
        ENNReal.ofReal ((C + 1 / Real.exp 1) / Real.log n) := by sorry

end Z2PostSamp
