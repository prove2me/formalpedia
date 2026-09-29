-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
-- name    : Cryptography_ZeroKnowledge_SchnorrGroupProtocol
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:30:12.594066+00:00
-- url     : https://prove2.me/theorems/aa67fe4b-a58e-45cd-b412-5e37b327442a
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_SchnorrGroupProtocol
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.SchnorrGroupProtocol`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean by skeleton subtraction
import Mathlib
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

namespace SchnorrGrp

variable {G : Type*} [CommGroup G] {q : ℕ}

/-! ### Exponentiation by a `ZMod q` scalar -/

/-- Exponentiation of a group element by a scalar in `ZMod q`, via the canonical
representative.  It is a homomorphism in the exponent exactly on `q`-torsion elements. -/
def gexp (h : G) (e : ZMod q) : G := h ^ e.val













/-! ### The protocol -/

/-- A protocol transcript in the group model: commitment `a ∈ G`, challenge `c` and
response `z` in `ZMod q`. -/
@[ext]
structure Transcript (G : Type*) (q : ℕ) where
  /-- The commitment. -/
  a : G
  /-- The challenge. -/
  c : ZMod q
  /-- The response. -/
  z : ZMod q

/-- The Schnorr verifier: accept `(a, c, z)` for public key `pub` iff `g ^ z = a * pub ^ c`. -/
def Accepts (g pub : G) (T : Transcript G q) : Prop :=
  gexp g T.z = T.a * gexp pub T.c

/-- The honest prover's transcript with randomness `r` on challenge `c`. -/
def honest (g : G) (x r c : ZMod q) : Transcript G q := ⟨gexp g r, c, r + c * x⟩

/-- The honest-verifier simulator: choose the response `z` at random and back-solve the
commitment as `g ^ z * (pub ^ c)⁻¹`.  It uses no witness. -/
def simulate (g pub : G) (c z : ZMod q) : Transcript G q :=
  ⟨gexp g z * (gexp pub c)⁻¹, c, z⟩


/-- The Schnorr extractor applied to two forking transcripts. -/
def extract (c₁ z₁ c₂ z₂ : ZMod q) : ZMod q := (z₁ - z₂) * (c₁ - c₂)⁻¹




/-! ### Honest-verifier zero knowledge -/



/-- The randomness-to-response bijection `r ↦ r + c * x` underlying perfect HVZK. -/
def hvzkEquiv (x c : ZMod q) : ZMod q ≃ ZMod q where
  toFun r := r + c * x
  invFun z := z - c * x
  left_inv := by intro r; simp
  right_inv := by intro z; simp




/-! ### Quantitative soundness error -/



end SchnorrGrp


