-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupBridge
-- name    : Cryptography_ZeroKnowledge_SchnorrGroupBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:30:47.200171+00:00
-- url     : https://prove2.me/theorems/15f41c72-7666-4168-b2b9-b279e2bf15c9
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_SchnorrGroupBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.SchnorrGroupBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/SchnorrGroupBridge.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_SchnorrIdentification
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Bridge: the catalog's additive Schnorr model is the group model at `Multiplicative (ZMod p)`

The catalog models Schnorr additively (`Cryptography.SchnorrIdentification`): the "group" is
`ZMod p`, the public key of `x` is `P.pk x = x * P.g`, and the verifier checks
`s * g = t + c * Y`.  `Cryptography.ZeroKnowledge.SchnorrGroupProtocol` models it
multiplicatively in an arbitrary commutative group of exponent `q`.

This file identifies the two: taking `G := Multiplicative (ZMod p)` and generator
`Multiplicative.ofAdd P.g`, the group-model exponentiation `gexp` *is* the additive model's
scalar multiplication, and the two verification predicates agree.  Consequently every
theorem proved in the group model specialises to the catalog's model, and conversely the
group-model machinery yields new results there — in particular the **distributional** form
of perfect honest-verifier zero knowledge (`hvzk_pmf_additive`), which strengthens the
catalog's counting form `SchnorrZK.hvzk_event_card_eq` to an equality of probability
distributions on transcripts.

## Main results

* `gexp_ofAdd` — `gexp (ofAdd a) e = ofAdd (e * a)`: the two scalar actions coincide.
* `orderOf_ofAdd_g` — the additive generator has multiplicative order `p`.
* `accepts_iff_Accepts` — the additive and group verification predicates agree.
* `completeness_of_group`, `special_soundness_of_group` — the catalog's completeness and
  extraction statements re-derived from the group model.
* `hvzk_pmf_additive` — new: perfect HVZK for the catalog's model as an equality of `PMF`s.
-/

namespace SchnorrGrp

open Multiplicative

variable (P : SchnorrParams)

instance : NeZero P.p := ⟨P.hp.out.ne_zero⟩








end SchnorrGrp


