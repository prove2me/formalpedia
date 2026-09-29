-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupInstances
-- name    : Cryptography_ZeroKnowledge_SchnorrGroupInstances
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:30:49.710141+00:00
-- url     : https://prove2.me/theorems/827cb008-5916-4138-ac3a-f5758262ae39
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_SchnorrGroupInstances
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.SchnorrGroupInstances`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/SchnorrGroupInstances.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Exact soundness error, unique responses, and a concrete instance of group-model Schnorr

`Cryptography.ZeroKnowledge.SchnorrGroupProtocol` develops the Schnorr Σ-protocol in an
abstract commutative group of exponent `q`.  This file

* sharpens the soundness analysis in a *cyclic group of prime order `q`*: there the
  cheating probability of a pre-committed pair `(a, z)` is **exactly** `1 / q`
  (`soundness_error_eq`), not merely at most `1 / q`;
* proves the *unique response* property (`unique_response`);
* exhibits a concrete group satisfying every standing hypothesis
  (`Multiplicative (ZMod q)` with generator `ofAdd 1`), so the theory is not vacuous, and
  instantiates completeness, extraction and zero knowledge there.

## Main results

* `gexp_bijective`, `gexp_surjective` — in a group of prime order `q`, a nontrivial element
  generates: `e ↦ h ^ e` is a bijection `ZMod q ≃ G`.
* `accepting_challenges_card_eq_one`, `soundness_error_eq` — exactly one challenge is
  accepting for a pre-committed `(a, z)`, so the soundness error is exactly `1 / q`.
* `unique_response` — for a fixed commitment and challenge the accepting response is unique.
* `schnorrGen_orderOf`, `instance_completeness`, `instance_extraction`, `instance_hvzk` —
  the concrete instance and the three protocol properties instantiated in it.
-/

namespace SchnorrGrp

/-! ### Cyclic groups of prime order: the soundness error is exactly `1/q` -/

section Cyclic

variable {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [Fact q.Prime]





end Cyclic


/-! ### A concrete instance: the cyclic group `Multiplicative (ZMod q)` -/

section Instance

variable (q : ℕ) [NeZero q]

/-- The concrete prime-order group used to instantiate the protocol. -/
abbrev SchnorrGroup : Type := Multiplicative (ZMod q)

/-- The canonical generator of `SchnorrGroup q`. -/
def schnorrGen : SchnorrGroup q := Multiplicative.ofAdd 1









end Instance

end SchnorrGrp


