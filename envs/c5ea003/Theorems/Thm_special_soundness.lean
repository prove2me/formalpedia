-- Prove2me | Theorems.Thm_special_soundness
-- name    : special_soundness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:09:50.558318+00:00
-- url     : https://prove2.me/theorems/74df8fe8-8e73-419f-959e-a0dac68caf49
-- title:
--   Special soundness.
-- statement:
--   **Special soundness.**  Two accepting transcripts sharing the commitment `t`
--   with distinct challenges determine the secret.
--
--   ```lean
--   theorem special_soundness(x t c₁ s₁ c₂ s₂ : ZMod P.p)
--       (h₁ : accepts P (P.pk x) (t, c₁, s₁))
--       (h₂ : accepts P (P.pk x) (t, c₂, s₂))
--       (hc : c₁ ≠ c₂) :
--       x = (c₁ - c₂)⁻¹ * (s₁ - s₂) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SchnorrIdentification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SchnorrIdentification.lean#L96

-- Thm stub generated from Cryptography/SchnorrIdentification.lean
import Mathlib
import Definitions.Def_Cryptography_SchnorrIdentification
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


attribute [instance] SchnorrParams.hp

open SchnorrParams



variable (P : SchnorrParams)

theorem special_soundness(x t c₁ s₁ c₂ s₂ : ZMod P.p)
    (h₁ : accepts P (P.pk x) (t, c₁, s₁))
    (h₂ : accepts P (P.pk x) (t, c₂, s₂))
    (hc : c₁ ≠ c₂) :
    x = (c₁ - c₂)⁻¹ * (s₁ - s₂) := by sorry
