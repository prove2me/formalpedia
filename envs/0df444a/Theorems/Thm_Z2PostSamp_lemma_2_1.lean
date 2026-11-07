-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_2_1
-- name    : Z2PostSamp.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:11.518417+00:00
-- url     : https://prove2.me/theorems/6b827612-79ef-45eb-ab27-4adb9c14c6e2
-- title:
--   Lemma 2.1 — independence Metropolis from a $(\delta,M)$-warm proposal: $\|QK^t-P\|_{\mathrm{TV}}\le\delta+\delta/M+e^{-t(1-\delta)/M}$
-- statement:
--   Let $P$ and $Q$ be strictly positive probability laws on a finite set, let $K$ be the transition kernel of the independence Metropolis process with target $P$ and proposal $Q$ (propose $z\sim Q$, accept with probability $\min\{1,P(z)Q(y)/(P(y)Q(z))\}$), and let $M\ge1$. Say that $Q$ is $(\delta,M)$-warm with respect to $P$ if
--
--   $$P\Big(\frac{dP}{dQ}>M\Big)=\delta .$$
--
--   Then for every integer $t\ge0$,
--
--   $$\big\|QK^t-P\big\|_{\mathrm{TV}}\le\delta+\frac\delta M+\exp\Big(-\frac{t(1-\delta)}M\Big).$$
--
--   The lemma reduces approximate posterior sampling to constructing a proposal whose density ratio to the target is bounded outside a set of small target mass.
--
--   **Formalization Note** Laws are functions on a finite type, $QK^t$ is the row vector `Q ᵥ* K^t`, and total variation is half the $\ell^1$ distance.
--
--   Differences from the source:
--   - encoding: Q is (δ, M)-warm with respect to P, i.e. P(dP/dQ > M) = δ → δ is a real with warmDelta P Q M = δ; reason: warmness is a definition of δ; the hypothesis is that definition
--   - encoding: probability measures on a finite set → strictly positive functions summing to one on a Fintype; reason: on a finite set a probability measure is its mass function
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 2.1, p.6, (2.1)–(2.2)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_IndepMetropolis

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 2.1 (independence Metropolis from a warm proposal).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 2.1, p.6: "For `M ≥ 1`, we say `Q` is `(δ, M)`-warm with respect to `P` if
`P(dP/dQ > M) = δ`. Let `K` be the transition kernel of the process `X_t`. If `Q` is `(δ, M)`-warm
with respect to `P`, then for every integer `t ≥ 0`, `‖QKᵗ − P‖_TV ≤ δ + δ/M + exp(−t(1 − δ)/M)`
(2.2)." The process (2.1), p.6: two strictly positive probability measures `P, Q` on a finite set,
`X_0 ∼ Q`, propose `z ∼ Q`, accept with probability `min{1, P(z)Q(y)/(P(y)Q(z))}`.

**Formalization Note.** `P, Q` are strictly positive functions summing to one on a finite type;
`δ` is the warmness level `warmDelta P Q M = Σ_{P(x)/Q(x) > M} P(x)` (warmness is a definition, so
the hypothesis is the equation defining `δ`). `QKᵗ` is the row vector `Q ᵥ* Kᵗ`. -/
theorem lemma_2_1 {α : Type} [Fintype α] [DecidableEq α] (P Q : α → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 < Q x) (hP1 : ∑ x, P x = 1) (hQ1 : ∑ x, Q x = 1)
    (M δ : ℝ) (hM : 1 ≤ M) (hδ : warmDelta P Q M = δ) (t : ℕ) :
    finTV (Q ᵥ* (imKernel P Q ^ t)) P ≤ δ + δ / M + Real.exp (-((t : ℝ) * (1 - δ)) / M) := by sorry

end Z2PostSamp
