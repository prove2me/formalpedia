-- Prove2me | Theorems.Thm_Z2PostSamp_theorem_1_1
-- name    : Z2PostSamp.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:58.626974+00:00
-- url     : https://prove2.me/theorems/090d6199-0052-4e75-81fa-1b458aa701f4
-- title:
--   Theorem 1.1 — a polynomial-time sampler with $\mathbb E_Y\|\widehat\mu(\cdot\mid Y)-\mu_Y\|_{\mathrm{TV}}\to0$ for every $\lambda>1$
-- statement:
--   Consider the $\mathbb Z_2$ synchronization model $Y=\frac\lambda{\sqrt n}\theta\theta^\top+Z$, with $\theta$ uniform on $\{-1,1\}^n$ and $Z$ the independent real symmetric Gaussian matrix with $\mathcal N(0,1)$ entries above the diagonal and $\mathcal N(0,2)$ entries on it, and let $\mu_Y=\mu_J$, $J=\frac\lambda{\sqrt n}Y$, be the posterior (1.1).
--
--   There is a randomized algorithm that takes $Y$ and the known parameter $\lambda$ as input and outputs a sample $\widehat\theta\sim\widehat\mu$, with running time polynomial in $n$ for each fixed $\lambda>1$, whose conditional output law $\widehat\mu(\cdot\mid Y)$ satisfies
--
--   $$\mathbb E_Y\big\|\widehat\mu(\cdot\mid Y)-\mu_Y\big\|_{\mathrm{TV}}\to0 .\tag{1.2}$$
--
--   In particular, $\|\widehat\mu(\cdot\mid Y)-\mu_Y\|_{\mathrm{TV}}=o_{\mathbb P}(1)$.
--
--   Precisely: there is one program $P$ of the randomized log-cost RAM with dyadic real oracle such that for every $\lambda>1$ there is $c$ with
--
--   1. on every $n\ge1$, every real $n\times n$ matrix $Y$ and every coin tape, $P$ halts on input $(Y,\lambda)$ with cost at most $c\,n^c$;
--   2. $\mathbb E_{(\theta,Z)}\|\widehat\mu(\cdot\mid Y)-\mu_Y\|_{\mathrm{TV}}\to0$;
--   3. for every $\varepsilon>0$, $\mathbb P_{(\theta,Z)}\big(\|\widehat\mu(\cdot\mid Y)-\mu_Y\|_{\mathrm{TV}}>\varepsilon\big)\to0$.
--
--   The result covers the whole weak-recovery regime $\lambda>1$, samples the full posterior including its global sign symmetry, and needs no side information. The running-time exponent may depend on $\lambda$.
--
--   **Formalization Note** The program is chosen before $\lambda$ and reads $Y$ and $\lambda$ only through clamped dyadic approximations, every requested bit being charged (the convention of §2, p.6). The output law is the coin-tape law of the decoded output at step budget $c\,n^c$, at which the machine has halted. $\mathbb E_Y$ is the lower Lebesgue integral of the total variation $\frac12\sum|\widehat\mu-\mu_Y|$ (published `lawTV`) over the law of $(\theta,Z)$.
--
--   Differences from the source:
--   - reading: a randomized algorithm (Algorithm 4) taking Y and λ as input → one program of the randomized log-cost RAM whose only access to Y and λ is the clamped dyadic oracle `approx`, charged its requested bits; input list [n], Y row-major then λ in the oracle; reason: the computational convention of §2 (p.6): dyadic approximations, cost includes all requested bits; the paper names no machine
--   - reading: running time polynomial in n for each fixed λ > 1 → ∃ program, ∀ λ > 1, ∃ c, cost ≤ c·n^c on every coin tape; reason: one algorithm with input λ whose exponent may depend on λ (p.2); worst case over tapes is the strongest reading
--   - generalization: the running time on the algorithm's inputs (observations of the model) → the cost bound for every n ≥ 1 and every real n × n matrix Y; reason: a bound on every input implies the bound on the model's inputs
--   - encoding: E_Y ‖μ̂(·|Y) − μ_Y‖_TV → 0 and ‖·‖_TV = o_P(1) → lower Lebesgue integral of lawTV over the law of (θ, Z(E)) tends to 0, and P(TV > ε) → 0 for every ε > 0; reason: the integrand is nonnegative; o_P(1) is convergence in probability
--   - encoding: the conditional output law μ̂(·|Y) → coin-tape law of the decoded output after c·n^c steps; reason: every step before halting costs at least 1, so at this budget the machine has halted and this is the output law
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Theorem 1.1, p.2, (1.1)–(1.2); §2 preamble, p.6; Algorithm 4 and App. A–B, pp.35–41

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Machine
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_SamplerIO

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Theorem 1.1 (efficient posterior sampling for ℤ₂ synchronization).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Theorem 1.1, p.2: "There is a randomized algorithm (see Algorithm 4) that takes `Y` and the
known parameter `λ` as input and outputs a sample `θ̂ ∼ μ̂`, with running time polynomial in `n` for
each fixed `λ > 1`, whose conditional output law `μ̂` satisfies `E_Y ‖μ̂(· | Y) − μ_Y‖_TV → 0` (1.2).
In particular, `‖μ̂(· | Y) − μ_Y‖_TV = o_P(1)`." The model is `Y = (λ/√n) θθᵀ + Z` (p.2) and
`μ_Y = μ_J`, `J = (λ/√n) Y` (1.1).

**Formalization Note.** "A randomized algorithm" is one program `P` of the randomized log-cost RAM
with dyadic real oracle (`Z2PostSamp.Machine`), chosen before `λ`; it receives the input list `[n]`
and reads `Y` and `λ` only through clamped dyadic approximations, every requested bit being charged
(§2 preamble, p.6). "Running time polynomial in `n` for each fixed `λ > 1`" is: for each `λ > 1`
there is `c` (the exponent may depend on `λ`, p.2) such that on **every** real matrix `Y`, every
`n ≥ 1` and **every** coin tape the program halts with log-cost at most `c·nᶜ` (worst case, not
expected, not with high probability). The output law `μ̂(· | Y)` is the coin-tape law of the decoded
output read at step budget `c·nᶜ` (by the first conjunct the machine has halted by then). `E_Y` is
the lower Lebesgue integral of the total variation `½ Σ |μ̂ − μ_Y|` over the law of `(θ, Z)`; the
`o_P(1)` clause is the third conjunct. -/
theorem theorem_1_1 :
    ∃ P : Program, ∀ lam : ℝ, 1 < lam → ∃ c : ℕ,
      (∀ n : ℕ, 1 ≤ n → ∀ Y : Matrix (Fin n) (Fin n) ℝ, ∀ ω : ℕ → Bool,
        HaltsWithin P (oracleOf n Y lam) [n] ω (c * n ^ c)) ∧
      Tendsto (fun n : ℕ => ∫⁻ p, ENNReal.ofReal
          (lawTV (outLaw P n (obsY n lam p.1 (Zmat p.2)) lam (c * n ^ c))
            (postY n lam (obsY n lam p.1 (Zmat p.2)))) ∂((signalLaw n).prod (noiseLaw n)))
        atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => ((signalLaw n).prod (noiseLaw n))
          {p | ε < lawTV (outLaw P n (obsY n lam p.1 (Zmat p.2)) lam (c * n ^ c))
            (postY n lam (obsY n lam p.1 (Zmat p.2)))}) atTop (𝓝 0) := by sorry

end Z2PostSamp
