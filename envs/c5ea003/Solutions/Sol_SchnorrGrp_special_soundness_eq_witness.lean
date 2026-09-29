-- Prove2me | solution 1 for SchnorrGrp.special_soundness_eq_witness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:04:30.866679+00:00
-- url     : https://prove2.me/submissions/bbe5e027-126f-4308-875b-246a13345eab

-- Sol generated from Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
import Theorems.Thm_SchnorrGrp_gexp_injective
import Theorems.Thm_SchnorrGrp_special_soundness_witness
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






theorem gexp_pow_q [NeZero q] {h : G} (hh : h ^ q = 1) (e : ZMod q) : (gexp h e) ^ q = 1 := by
  rw [gexp, ← pow_mul, mul_comm, pow_mul, hh, one_pow]








/-! ### The protocol -/










/-! ### Honest-verifier zero knowledge -/







/-! ### Quantitative soundness error -/




open SchnorrGrp in
theorem solution[Fact q.Prime] {g : G} (hg : g ^ q = 1)
    (horder : orderOf g = q) (x : ZMod q) (a : G) (c₁ z₁ c₂ z₂ : ZMod q)
    (h₁ : Accepts g (gexp g x) ⟨a, c₁, z₁⟩) (h₂ : Accepts g (gexp g x) ⟨a, c₂, z₂⟩)
    (hc : c₁ ≠ c₂) :
    extract c₁ z₁ c₂ z₂ = x :=
  gexp_injective horder
    (special_soundness_witness hg (gexp_pow_q hg x) a c₁ z₁ c₂ z₂ h₁ h₂ hc)
