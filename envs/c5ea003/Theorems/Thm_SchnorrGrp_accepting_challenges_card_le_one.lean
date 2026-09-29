-- Prove2me | Theorems.Thm_SchnorrGrp_accepting_challenges_card_le_one
-- name    : SchnorrGrp.accepting_challenges_card_le_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:59:14.928615+00:00
-- url     : https://prove2.me/theorems/894f2a1a-2475-42ea-8c53-c9759a5b4796
-- title:
--   A commitment/response pair `(a, z)` fixed *before* the challenge is accepted for at most
-- statement:
--   A commitment/response pair `(a, z)` fixed *before* the challenge is accepted for at most
--   one challenge, provided the public key is nontrivial.
--
--   ```lean
--   theorem SchnorrGrp.accepting_challenges_card_le_one[Fact q.Prime] {g pub : G} (hpub : pub ^ q = 1)
--       (hpub1 : pub ≠ 1) (a : G) (z : ZMod q) :
--       (Finset.univ.filter (fun c : ZMod q => Accepts g pub ⟨a, c, z⟩)).card ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean#L235

-- Thm stub generated from Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Schnorr identification Σ-protocol in a genuine cyclic group

The catalog already contains an *additive* model of Schnorr (`Cryptography.SchnorrIdentification`
and the files in `Cryptography/ZeroKnowledge/`), where the "group" is the field `ZMod p`,
"scalar multiplication" is field multiplication and the public key of `x` is `x * g`.  That
model is algebraically convenient but it hides the actual group-theoretic content of the
protocol: in the real scheme the prover works in a cyclic group `G` of prime order `q`, the
commitment is `g ^ r`, the public key is `g ^ x`, and verification reads `g ^ z = a * pub ^ c`
with the exponents living in `ZMod q` while the group operation lives in `G`.

This file develops that faithful multiplicative model:

* `gexp h e = h ^ e.val` is exponentiation of a group element by a `ZMod q` scalar; it is
  well defined as a homomorphism precisely on the `q`-torsion (`h ^ q = 1`), which is the
  standing hypothesis throughout.
* `SchnorrGrp.Accepts g pub T` is the verification equation `g ^ z = a * pub ^ c`.

## Main results

* `gexp_add`, `gexp_mul`, `gexp_sub`, `gexp_injective` — the exponentiation API.
* `completeness` — the honest prover `(g ^ r, c, r + c * x)` is always accepted.
* `special_soundness_witness` — two accepting transcripts sharing a commitment with distinct
  challenges yield a genuine discrete logarithm of an *arbitrary* public key `pub`
  (only `pub ^ q = 1` is needed), i.e. knowledge soundness with extractor
  `(z₁ - z₂) * (c₁ - c₂)⁻¹`.
* `special_soundness_eq_witness` — specialised to `pub = g ^ x`, the extractor returns `x`.
* `simulate_accepts`, `honest_eq_simulate`, `hvzk_equiv`, `hvzk_pmf` — perfect
  honest-verifier zero knowledge: the simulator's output is accepting, matches the honest
  transcript under an explicit bijection of the randomness, and induces *literally the same
  distribution* as the honest prover (equality of `PMF`s).
* `accepting_challenges_card_le_one`, `soundness_error_le` — the quantitative soundness
  error: a commitment/response pair fixed in advance is accepted for at most one challenge,
  so a cheating prover succeeds with probability at most `1 / q`.
-/

open SchnorrGrp

variable {G : Type*} [CommGroup G] {q : ℕ}

/-! ### Exponentiation by a `ZMod q` scalar -/














/-! ### The protocol -/










/-! ### Honest-verifier zero knowledge -/







/-! ### Quantitative soundness error -/

open scoped Classical in

theorem SchnorrGrp.accepting_challenges_card_le_one[Fact q.Prime] {g pub : G} (hpub : pub ^ q = 1)
    (hpub1 : pub ≠ 1) (a : G) (z : ZMod q) :
    (Finset.univ.filter (fun c : ZMod q => Accepts g pub ⟨a, c, z⟩)).card ≤ 1 := by sorry
