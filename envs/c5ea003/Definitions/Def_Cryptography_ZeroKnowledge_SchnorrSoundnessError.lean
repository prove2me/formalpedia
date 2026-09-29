-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_SchnorrSoundnessError
-- name    : Cryptography_ZeroKnowledge_SchnorrSoundnessError
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:31:04.150067+00:00
-- url     : https://prove2.me/theorems/192339c0-1d83-4296-9e6c-20cfd9b27c0a
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_SchnorrSoundnessError
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.SchnorrSoundnessError`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/SchnorrSoundnessError.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_SchnorrIdentification

/-!
# The exact soundness error of the Schnorr Σ-protocol is `1/p`

A cheating prover that does not know the discrete logarithm must commit to a value `t`
*before* seeing the challenge `c`, and can only send a single pre-chosen response `s`. We
prove that, for any nonzero public key `Y`, such a pre-committed pair `(t, s)` is accepted
for **exactly one** challenge `c` out of the `p` possible challenges. Hence the soundness
error — the maximal cheating probability of a witness-free prover over a uniform
challenge — is exactly `1/p`.

## Main results

* `accepts_iff_response` — for fixed `t, c, Y`, the accepting response is unique:
  `accepts P Y (t, c, s) ↔ s = (t + c * Y) * P.g⁻¹`.
* `winning_challenges_card` — for `Y ≠ 0` and fixed `(t, s)`, exactly one challenge is
  accepting: the filtered `Finset` over `ZMod p` has cardinality `1`.
* `challenge_space_card` — the challenge space `ZMod p` has cardinality `p`.
* `soundness_error` — the cheating probability `card winning / card all = 1 / p`.

-- !-- Lab Notes -- !--
Hypothesis (SE1): rewriting acceptance `s • g = t + c • Y` as a linear equation in the
challenge `c` (with `Y` invertible) yields a unique solution `c = (s • g - t) • Y⁻¹`, so the
winning-challenge set is a singleton.
Experiment: define `winningChallenge` explicitly, prove the membership iff over a prime
field, then compute the filtered `Finset.card` via `Finset.card_eq_one`. Outcome:
confirmed; the only structural inputs are that `ZMod p` is a field (`p` prime) and `Y ≠ 0`.
Analysis: this is the *quantitative* counterpart of special soundness — two winning
challenges would contradict the singleton, forcing extraction. Critique: the bound is tight
(`= 1/p`, not merely `≤`), and degenerates correctly: if `Y = 0` the prover either always
or never wins, so the `Y ≠ 0` hypothesis is essential and stated. Synthesis: combined with
`SchnorrKnowledgeSoundness`, the protocol is a proof of knowledge with knowledge error `1/p`.
-/

namespace SchnorrSE

open scoped Classical

variable (P : SchnorrParams)

/-- The unique accepting response for commitment `t`, challenge `c`, public key `Y`. -/
def responseFor (Y t c : ZMod P.p) : ZMod P.p := (t + c * Y) * P.g⁻¹

/-- The unique winning challenge for a pre-committed pair `(t, s)` against `Y ≠ 0`. -/
def winningChallenge (Y t s : ZMod P.p) : ZMod P.p := (s * P.g - t) * Y⁻¹

/-
**Uniqueness of the response.** For fixed `t, c, Y` the verifier accepts exactly one
response.
-/

/-
**Uniqueness of the winning challenge.** For `Y ≠ 0` and a pre-committed `(t, s)`,
acceptance holds for exactly the challenge `winningChallenge`.
-/

/-
**Exactly one winning challenge.** For `Y ≠ 0` and fixed `(t, s)`, the set of accepting
challenges in `ZMod p` has cardinality `1`.
-/

/-
The challenge space `ZMod p` has cardinality `p`.
-/

/-
**Soundness error `= 1/p`.** The fraction of challenges on which a witness-free,
pre-committed prover `(t, s)` succeeds equals `1 / p`.
-/

end SchnorrSE


