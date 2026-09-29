-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_Graph3ColoringAmplification
-- name    : Cryptography_ZeroKnowledge_Graph3ColoringAmplification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:57:31.097837+00:00
-- url     : https://prove2.me/theorems/79c08464-f802-4716-9c26-29d6639d7598
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_Graph3ColoringAmplification
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.Graph3ColoringAmplification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/Graph3ColoringAmplification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3Coloring

/-!
# Soundness Amplification for the GMW Graph 3-Colouring Proof

A single round of the Goldreich–Micali–Wigderson protocol has only a *constant*
soundness gap: against an improper committed colouring the verifier rejects with
probability `≥ 1/|E|` (proved in `Cryptography.ZeroKnowledge.Graph3Coloring`).
This file shows how **sequential repetition** drives the cheating probability to
zero.

We model the one-round acceptance probability of a (cheating) prover committed to
an improper colouring `c'` as the fraction of edges whose endpoints receive
*distinct* colours (those are exactly the edges the verifier fails to catch).
Running `k` independent rounds multiplies this probability, giving `p ^ k`.

## Main results

* `roundAcceptProb_nonneg` / `roundAcceptProb_le_one` — the acceptance probability
  is a genuine probability in `[0, 1]`.
* `roundAcceptProb_lt_one` — against an **improper** colouring the acceptance
  probability is strictly below `1`.
* `roundAcceptProb_le_one_sub` — the quantitative gap: acceptance is at most
  `1 - 1/|E|`.
* `soundness_amplification` — **the amplification theorem**: the `k`-round
  cheating probability `p ^ k` tends to `0` as `k → ∞`. Hence for any target
  error the verifier can be convinced, on a false statement, with vanishing
  probability by repeating the protocol.
* `soundness_amplification_exists` — the `∀ ε > 0, ∃ k` reformulation.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The constant per-round soundness gap `1/|E|` of GMW
can be amplified to an arbitrarily small error by sequential repetition; formally,
the `k`-round acceptance probability `p ^ k` converges to `0`, with `p < 1`
whenever the committed colouring is improper.

Experiment (Experimenter): Defined `roundAcceptProb` as the fraction of "uncaught"
edges. The key inequality `roundAcceptProb < 1` was reduced, via
`Finset.filter_card_add_filter_neg_card_eq_card`, to the existence of at least one
caught edge — precisely `soundness_catch_card` from the base file. Convergence
then follows from `tendsto_pow_atTop_nhds_zero_of_lt_one` applied to `0 ≤ p < 1`.

Analysis (Analyst): The proof cleanly separates the *combinatorial* content (there
is a caught edge) from the *analytic* content (geometric decay). Reusing
`soundness_catch_card` demonstrates that the base soundness lemma is exactly the
hypothesis needed for amplification. The `∃ k` corollary makes the practical
guarantee explicit. The "true but hard" boundary avoided is a full probabilistic
model of adaptive provers across rounds; the multiplicative independence model is
the standard and sufficient one for sequential repetition.

Critique (Critic): `roundAcceptProb_lt_one` genuinely needs the improperness
hypothesis (checked: it feeds `soundness_catch_card`); dropping it makes the claim
false (a proper colouring is always accepted). `soundness_amplification` is not a
`decide`/`norm_num` fact — it invokes a real convergence theorem. The probability
`p` is bounded in `[0,1]` so the statement is not vacuous.

Synthesis (PI): This upgrades the single-round soundness gap into the full
soundness guarantee of the interactive proof system: false statements are
accepted with probability `→ 0`.
-- !-- Lab Notes -- !--
-/

namespace ZK.Graph3Coloring

open Finset

/-- The one-round **acceptance probability** of a prover committed to colouring
`c'`: the fraction of edges whose endpoints get distinct colours (the edges on
which the verifier accepts). -/
noncomputable def roundAcceptProb {V : Type*} (E : Finset (V × V)) (c' : V → Fin 3) : ℝ :=
  ((E.filter (fun e => c' e.1 ≠ c' e.2)).card : ℝ) / E.card







end ZK.Graph3Coloring


