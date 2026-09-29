-- Prove2me | Definitions.Def_Cryptography_SchnorrIdentification
-- name    : Cryptography_SchnorrIdentification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:06.711308+00:00
-- url     : https://prove2.me/theorems/93bce318-7bdf-45ce-a4e8-f7425443dfb3
-- title:
--   Aether Catalog definitions — Cryptography_SchnorrIdentification
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.SchnorrIdentification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/SchnorrIdentification.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Schnorr identification Σ-protocol

An additive model of the Schnorr identification scheme over a prime field.  The
"group" is `ZMod p` with a fixed nonzero generator `g`; "scalar times group
element" is field multiplication, and the public key of the secret `x` is
`pk x = x * g`.

A transcript is a triple `(t, c, s)` (commitment, challenge, response) and the
verifier accepts iff `s * g = t + c * Y`.

## Main results

* `completeness` — the honest prover is always accepted;
* `special_soundness` — two accepting transcripts with a common commitment and
  distinct challenges determine the secret;
* `sim_accepts` — the witness-free simulator produces accepting transcripts;
* `honestSimEquiv`, `hvzk_bijection` — honest and simulated transcripts are
  matched by an explicit bijection of the randomness, which is perfect
  honest-verifier zero knowledge in its combinatorial form.
-/

/-- Public parameters of the Schnorr identification protocol: a prime `p` and a
nonzero generator `g` of the additive model `ZMod p`. -/
structure SchnorrParams where
  /-- The prime modulus. -/
  p : ℕ
  /-- `p` is prime, so `ZMod p` is a field. -/
  hp : Fact (Nat.Prime p)
  /-- The generator. -/
  g : ZMod p
  /-- The generator is nonzero. -/
  hg : g ≠ 0

attribute [instance] SchnorrParams.hp

namespace SchnorrParams

/-- The public key associated with the secret `x`. -/
def pk (P : SchnorrParams) (x : ZMod P.p) : ZMod P.p := x * P.g

end SchnorrParams

variable (P : SchnorrParams)

/-- A protocol transcript: commitment, challenge, response. -/
@[ext]
structure Transcript (P : SchnorrParams) where
  /-- The commitment. -/
  t : ZMod P.p
  /-- The challenge. -/
  c : ZMod P.p
  /-- The response. -/
  s : ZMod P.p

/-- The verifier: the transcript `(t, c, s)` is accepted for the public key `Y`
iff `s * g = t + c * Y`. -/
def accepts (P : SchnorrParams) (Y : ZMod P.p)
    (T : ZMod P.p × ZMod P.p × ZMod P.p) : Prop :=
  T.2.2 * P.g = T.1 + T.2.1 * Y

/-- The honest transcript produced with randomness `r` on challenge `c`. -/
def honestTranscript (x r c : ZMod P.p) : Transcript P :=
  ⟨r * P.g, c, r + c * x⟩

/-- The simulated transcript: pick the challenge `c` and the response `s`, then
back-solve the commitment. -/
def simTranscript (x c s : ZMod P.p) : Transcript P :=
  ⟨s * P.g - c * P.pk x, c, s⟩





/-- The randomness ↔ response bijection `(r, c) ↦ (r + c * x, c)` underlying
perfect honest-verifier zero knowledge. -/
def honestSimEquiv (x : ZMod P.p) : (ZMod P.p × ZMod P.p) ≃ (ZMod P.p × ZMod P.p) where
  toFun rc := (rc.1 + rc.2 * x, rc.2)
  invFun sc := (sc.1 - sc.2 * x, sc.2)
  left_inv := by intro rc; simp
  right_inv := by intro sc; simp


