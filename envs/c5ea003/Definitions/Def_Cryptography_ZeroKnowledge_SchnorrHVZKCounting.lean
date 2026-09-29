-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_SchnorrHVZKCounting
-- name    : Cryptography_ZeroKnowledge_SchnorrHVZKCounting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:30:56.692237+00:00
-- url     : https://prove2.me/theorems/81971b0a-9051-48de-a783-5d95783efec4
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_SchnorrHVZKCounting
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.SchnorrHVZKCounting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/SchnorrHVZKCounting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_SchnorrIdentification

/-!
# Perfect HVZK as exact equality of event probabilities

The catalog's `hvzk_bijection` shows the honest transcript on randomness/challenge `(r, c)`
equals the simulated transcript on the image of `(r, c)` under the explicit bijection
`honestSimEquiv`. Here we upgrade that pointwise identity to its statistical meaning over
the finite probability space: for **every** event `E` on transcripts, the honest and
simulated transcripts assign it the *same count*, hence the same probability under the
uniform distribution. This is the precise statement of *perfect* honest-verifier
zero-knowledge.

## Main results

* `hvzk_event_card_eq` — for any decidable event `E`, the number of honest
  randomness/challenge pairs landing in `E` equals the number of simulator
  response/challenge pairs landing in `E`.
* `hvzk_probability_eq` — the same equality phrased as identical event probabilities
  (counts divided by the size `p²` of the sample space).

-- !-- Lab Notes -- !--
Hypothesis (ZK1): the catalog bijection `honestSimEquiv` is measure-preserving on the
uniform space, so honest and simulated transcripts induce identical event probabilities.
Experiment: transport the filtered `Finset` along `honestSimEquiv` using `Finset.card_bij`
(or `Finset.card_nbij'`), with the pointwise identity supplied by `hvzk_bijection`. Outcome:
confirmed; the bijection sends an honest index `(r, c)` to a simulator index `(s, c)` while
preserving the transcript, so the two filtered sets are in card-preserving correspondence.
Analysis: this is the difference between "the simulator can output every honest transcript"
(pointwise) and "it outputs them with the same probability" (statistical) — only the latter
is *perfect* zero-knowledge. Critique: the result is event-agnostic (`E` arbitrary), so no
distinguisher, however adaptive on the transcript, gains any advantage; the equality is
exact, not statistical-distance-bounded. Synthesis: together with completeness and
knowledge soundness, Schnorr is a perfect-HVZK proof of knowledge.
-/

namespace SchnorrZK

variable (P : SchnorrParams)

instance instNeZeroP : NeZero P.p := ⟨Nat.Prime.ne_zero P.hp.out⟩

open scoped Classical

/-
**Perfect HVZK, counting form.** For any event `E` on transcripts, the number of honest
randomness/challenge pairs `(r, c)` whose honest transcript lies in `E` equals the number of
simulator response/challenge pairs `(s, c)` whose simulated transcript lies in `E`.
-/

/-
**Perfect HVZK, probability form.** Dividing the equal counts by the size `p²` of the
uniform sample space, the honest and simulated transcripts assign every event the same
probability.
-/

end SchnorrZK


