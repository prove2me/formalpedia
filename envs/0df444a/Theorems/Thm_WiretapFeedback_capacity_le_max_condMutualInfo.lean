-- Prove2me | Theorems.Thm_WiretapFeedback_capacity_le_max_condMutualInfo
-- name    : WiretapFeedback.capacity_le_max_condMutualInfo
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:05:22.790984+00:00
-- url     : https://prove2.me/theorems/2242f6db-cc21-441b-8f1e-80d024549567
-- title:
--   Theorem 1 — $C_{\epsilon,\delta}\le\max_{P_X}I(X\wedge Y|Z)$ for the wiretap channel with public feedback
-- statement:
--   Let $W:\mathcal X\to\mathcal Y\times\mathcal Z$ be a discrete memoryless wiretap channel on finite alphabets (not necessarily degraded), in which the legitimate receiver may send noiseless public feedback to the transmitter. For $0\le\epsilon,\delta$ with $\epsilon+\delta<1$, the $(\epsilon,\delta)$-wiretap capacity is bounded above as
--   $$
--   C_{\epsilon,\delta}\le\max_{P_X}I(X\wedge Y|Z),
--   $$
--   where $I(X\wedge Y|Z)$ is the conditional mutual information (in bits) of $P_{XYZ}=P_XW$.
--
--   This is a strong converse: the bound holds for every fixed error probability $\epsilon$ and secrecy parameter $\delta$ with $\epsilon+\delta<1$, not only as $\epsilon,\delta\to0$. For a degraded wiretap channel it matches Wyner's achievable rate and so characterizes $C_{\epsilon,\delta}$ in that range.
--
--   **Formalization Note** $C_{\epsilon,\delta}$ is the extended-real supremum of achievable rates, over codes with randomized encoders and randomized feedback over an arbitrary feedback alphabet; the maximum over input distributions is an extended-real supremum (attained on the compact simplex).
--
--   Differences from the source:
--   - encoding: C_{ϵ,δ} = sup of achievable rates (0 if none) → sSup in EReal (⊥ if none); reason: both are ≤ the non-negative right-hand side; the inequality is unchanged
--   - encoding: max over P_X → ⨆ over FinDist X in EReal; reason: attained on the compact simplex; same value
--   - encoding: log base fixed by ⌊2^{nR}⌋, variation distance with factor ½ → Real.rpow 2, Nat.floor; tvDist in ℝ≥0∞ with factor 2⁻¹; reason: Lean convention; same quantities
--   - encoding: (possibly randomized) encoder and feedback mappings, time index t = 1, …, n, messages {1, …, N} → deterministic maps of independent local randomness Ux, Uy of arbitrary type (paper's own representation, proof of Lemma 7), arbitrary feedback alphabet, 0-based rounds, Fin N; reason: Lean convention; the same class of codes
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, p.2, Theorem 1

import Mathlib
import Definitions.Def_WildeQIT_condMutualInfo
import Definitions.Def_WiretapFeedback_wiretapCapacity
import Definitions.Def_WiretapFeedback_jointLaw

namespace WiretapFeedback

/-- **Theorem 1** (Hayashi–Tyagi–Watanabe, *Strong Converse for a Degraded Wiretap Channel via
Active Hypothesis Testing*, arXiv:1410.0443v1, p. 2). For `0 ≤ ϵ, δ` with `ϵ + δ < 1`, the
`(ϵ, δ)`-wiretap capacity (with noiseless public feedback) is bounded above as
`C_{ϵ,δ} ≤ max_{P_X} I(X ∧ Y | Z)`.

Here `W : X → Y × Z` is any discrete memoryless wiretap channel on finite alphabets (not
necessarily degraded), and `I(X ∧ Y | Z)` is computed for `P_{XYZ} = P_X W`.

**Formalization Note** Base-2 logarithms (rates are defined through `⌊2^{nR}⌋`). `C_{ϵ,δ}` is the
`EReal` supremum `wiretapCapacity` over codes with randomized encoders and randomized public
feedback over an arbitrary feedback alphabet; `max_{P_X}` is `⨆` in `EReal` over all input
distributions (attained, on the compact simplex). -/
theorem capacity_le_max_condMutualInfo {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (W : WildeQIT.Channel X (Y × Z)) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hεδ : ε + δ < 1) :
    wiretapCapacity W ε δ ≤
      ⨆ p : WildeQIT.FinDist X, ((WildeQIT.condMutualInfo (jointLaw p W) : ℝ) : EReal) := by sorry

end WiretapFeedback
