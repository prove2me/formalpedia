-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_2_4
-- name    : Z2PostSamp.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:09.982421+00:00
-- url     : https://prove2.me/theorems/ed9ccd98-af65-46b6-b5c9-b396076711ed
-- title:
--   Lemma 2.4 — the domains $\mathcal K_k$ are nonempty compact convex, and on $G_k$: $\|J\|_{\mathrm{op}}\le\lambda^2+10\lambda$, $m^{(k)}\in\mathcal K_k$, $\nabla^2\Phi_k\succeq\kappa_\lambda I$
-- statement:
--   Fix $\lambda>1$. There is a choice of the tuning record such that the domains $\mathcal K_k(x_{S_k})$ of (2.15) are nonempty, compact and convex for every input prefix. Moreover there are a constant $\kappa_\lambda>0$ and, along a posterior-distributed revealing path, events $G_k\in\mathcal H_k$ with
--
--   $$b_n:=\mathbb P\Big(\bigcup_{k=k_0}^{n-1}G_k^c\Big)=o(1),$$
--
--   such that on $G_k$ ($k_0\le k<n$):
--
--   1. $\|J\|_{\mathrm{op}}\le\lambda^2+10\lambda$;
--   2. $m^{(k)}(\theta_{S_k})\in\mathcal K_k(\theta_{S_k})$;
--   3. $\nabla^2_u\Phi_k(u;\theta_{S_k})\succeq\kappa_\lambda I$ for every $u\in\mathcal K_k(\theta_{S_k})$.
--
--   Both $\Phi_k(\cdot;\theta_{S_k})$ and $\mathcal K_k(\theta_{S_k})$ are built from the target prefix. The Hessian bound is uniform over the optimization variable in the domain; the record does not depend on $n$. This is the local strong convexity that makes the TAP optimization of Algorithm 2 accurate.
--
--   **Formalization Note** The record is a valid record in the sense of p.10. "Along a posterior-distributed revealing path" is the planted law of $(\theta,Z,I)$; $G_k\in\mathcal H_k$ is measurability for $\mathcal H_k$. $m^{(k)}$ is the conditional mean restricted to $R_k$; $\succeq\kappa I$ is $\kappa\sum_{i\in R_k}v_i^2\le v^\top\nabla^2_u\Phi_k\,v$ for every $v$, with the explicit Hessian form (the second derivative for the symmetric $J$ of the model).
--
--   Differences from the source:
--   - generalization: the domains are nonempty, compact and convex for every input prefix x_{S_k} → for every n, every matrix J (not only symmetric ones), every order I, configuration x and k; reason: covers every input the sampler can receive; the paper's inputs are a subset
--   - reading: along a posterior-distributed revealing path → under the planted law of (θ, Z, I); reason: §2 preamble, p.5 and Lemma 3.1
--   - encoding: ∇²_u Φ_k ⪰ κ_λ I on 𝒦_k → κ Σ_{R_k} v_i² ≤ tapHessQ (explicit second-derivative form) for every u ∈ 𝒦_k and every v; reason: for symmetric J the form is the Hessian; ⪰ is the order of quadratic forms
--   - reading: the domains (2.15) and centres of §2.3 (with the safeguards of App. A available and numerical routines of App. B) → the exact-arithmetic objects of §2.3, without safeguards or rounding; reason: Lemma 2.4 is stated for the construction of §2.3 and proved in §3.2; p.36 shows the numerical perturbations are absorbed by the margins
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 2.4, p.11; (2.15), p.11

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_TAP
import Definitions.Def_Z2PostSamp_Construction

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 2.4 (domains and strong convexity along the revealing path).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 2.4, p.11: "Fix `λ > 1`. There is a choice of the fixed tuning record above such that
the domains `𝒦_k(x_{S_k})` defined in (2.15) are nonempty, compact, and convex for every input prefix
`x_{S_k}`. Moreover, there is a constant `κ_λ > 0` and, along a posterior-distributed revealing path,
events `G_k ∈ ℋ_k` such that `b_n := P(∪_{k=k₀}^{n−1} G_kᶜ) = o(1)`, and, on `G_k`,
`‖J‖_op ≤ λ² + 10λ`, `m^{(k)}(θ_{S_k}) ∈ 𝒦_k(θ_{S_k})`, `∇²_u Φ_k(u; θ_{S_k}) ⪰ κ_λ I` for every
`u ∈ 𝒦_k(θ_{S_k})`."

**Formalization Note.** The record is valid (p.10) and independent of `n`; the domain clause holds
for every `n`, every matrix `J`, order `I`, configuration `x` and `k`. "Along a posterior-distributed
revealing path" is the planted law of `(θ, Z, I)` (§2 preamble, p.5); `G_k ∈ ℋ_k` is measurability
for `ℋ_k`. `‖J‖_op` is the `ℓ²→ℓ²` operator norm. `m^{(k)}` is the conditional mean restricted to
`R_k`, and `⪰ κI` is the inequality of quadratic forms `κ Σ_{R_k} v_i² ≤ vᵀ ∇²_u Φ_k v`. -/
theorem lemma_2_4 (lam : ℝ) (hlam : 1 < lam) :
    ∃ rec : TuningRecord, rec.Valid ∧
      (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ),
        (Kdom lam rec J I x k).Nonempty ∧ IsCompact (Kdom lam rec J I x k) ∧
          Convex ℝ (Kdom lam rec J I x k)) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∃ G : (n : ℕ) → ℕ → Set (PΩ n),
        (∀ n k, MeasurableSet[Hk n lam k] (G n k)) ∧
        Tendsto (fun n => plantedLaw n (⋃ k ∈ Finset.Ico (k0 n lam) n, (G n k)ᶜ)) atTop (𝓝 0) ∧
        ∀ n k : ℕ, k0 n lam ≤ k → k < n → ∀ ω ∈ G n k,
          opNorm (Jof n lam ω) ≤ lam ^ 2 + 10 * lam ∧
          onR ω.2.2 k (condMean (Jof n lam ω) ω.2.2 ω.1 k) ∈
            Kdom lam rec (Jof n lam ω) ω.2.2 ω.1 k ∧
          ∀ u ∈ Kdom lam rec (Jof n lam ω) ω.2.2 ω.1 k, ∀ v : Fin n → ℝ,
            κ * ∑ i ∈ Rset ω.2.2 k, v i ^ 2 ≤ tapHessQ lam (Jof n lam ω) ω.2.2 k u v := by sorry

end Z2PostSamp
