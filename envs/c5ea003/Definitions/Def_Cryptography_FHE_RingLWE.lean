-- Prove2me | Definitions.Def_Cryptography_FHE_RingLWE
-- name    : Cryptography_FHE_RingLWE
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:38:45.900934+00:00
-- url     : https://prove2.me/theorems/5e430c6d-0be3-4d90-a5c8-73db0f4d7d03
-- title:
--   Aether Catalog definitions — Cryptography_FHE_RingLWE
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FHE.RingLWE`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FHE/RingLWE.lean by skeleton subtraction
import Mathlib

/-!
# Ring-LWE homomorphic encryption: algebra, security reduction, and bootstrapping

This file develops a kernel-checked abstraction of the standard Ring-LWE FHE
argument.  It separates three layers which concrete parameter sets must connect:

* the exact ring identity behind additive homomorphism;
* the game hop from decisional Ring-LWE to IND-CPA security;
* Gentry's bootstrapping principle, expressed as refreshed circuit evaluation.

The security result is a reduction theorem: its Ring-LWE hypotheses are explicit,
rather than an unproved assertion that Ring-LWE is hard.
-/

open Finset BigOperators

noncomputable section

namespace RingLWEFHE

/-! ## 1. Exact Ring-LWE ciphertext algebra -/

/-- A two-component Ring-LWE ciphertext.  Conventionally `a` is uniform and
`b = a*s + Δ*m + e`. -/
structure Ciphertext (R : Type*) where
  a : R
  b : R

variable {R : Type*} [CommRing R]

/-- The secret-key phase `b - a*s` of a Ring-LWE ciphertext. -/
def phase (s : R) (c : Ciphertext R) : R := c.b - c.a * s

/-- Componentwise ciphertext addition. -/
def addCipher (c d : Ciphertext R) : Ciphertext R :=
  ⟨c.a + d.a, c.b + d.b⟩

/-- A symbolic Ring-LWE encryption with explicit public component and error. -/
def encryptWith (s scale m a e : R) : Ciphertext R :=
  ⟨a, a * s + scale * m + e⟩




/-- Decryption applies a phase decoder after taking the secret-key phase. -/
def decryptWith {M : Type*} (s : R) (decodePhase : R → M)
    (c : Ciphertext R) : M := decodePhase (phase s c)

/-- Abstract decoding condition for a particular scaled message and error. -/
def Decodes (decodePhase : R → R) (scale m e : R) : Prop :=
  decodePhase (scale * m + e) = m


/-! ## 2. Noise accumulation and a concrete additive correctness corollary -/


/-- A threshold decoder specification: every error of magnitude below `T`
decodes its intended scaled message. -/
def CorrectBelow (decodePhase : ℤ → ℤ) (scale T : ℤ) : Prop :=
  ∀ m e, |e| < T → Decodes decodePhase scale m e


/-! ## 3. Conditional security under decisional Ring-LWE -/

/-- A finite probability mass function, used to state statistical game hops. -/
structure FinitePMF (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

/-- The `ℓ¹` distance (twice statistical distance) between finite games. -/
def gameGap {Ω : Type*} [Fintype Ω] (P Q : FinitePMF Ω) : ℝ :=
  ∑ x, |P.mass x - Q.mass x|




/-! ## 4. Gentry bootstrapping as refreshed evaluation -/

/-- Arithmetic circuits over a message ring. -/
inductive Circuit (M : Type*) where
  | input : ℕ → Circuit M
  | const : M → Circuit M
  | add : Circuit M → Circuit M → Circuit M
  | mul : Circuit M → Circuit M → Circuit M

/-- Plaintext circuit semantics. -/
def Circuit.eval {M : Type*} [Semiring M] (ρ : ℕ → M) : Circuit M → M
  | .input i => ρ i
  | .const m => m
  | .add f g => f.eval ρ + g.eval ρ
  | .mul f g => f.eval ρ * g.eval ρ

/-- A somewhat homomorphic scheme equipped with a refresh operation.
The local gate laws only need to hold on the ciphertexts supplied to them;
refresh correctness is the bootstrapping hypothesis. -/
structure BootstrappableScheme (M C : Type*) [Semiring M] where
  enc : M → C
  dec : C → M
  add : C → C → C
  mul : C → C → C
  refresh : C → C
  enc_correct : ∀ m, dec (enc m) = m
  add_correct : ∀ c d, dec (add c d) = dec c + dec d
  mul_correct : ∀ c d, dec (mul c d) = dec c * dec d
  refresh_correct : ∀ c, dec (refresh c) = dec c

variable {M C : Type*} [Semiring M]




/-- Evaluate a circuit homomorphically, refreshing after every gate. -/
def Circuit.evalEncrypted (S : BootstrappableScheme M C)
    (ρ : ℕ → C) : Circuit M → C
  | .input i => S.refresh (ρ i)
  | .const m => S.refresh (S.enc m)
  | .add f g => S.refresh (S.add (f.evalEncrypted S ρ) (g.evalEncrypted S ρ))
  | .mul f g => S.refresh (S.mul (f.evalEncrypted S ρ) (g.evalEncrypted S ρ))


/-! ## 5. Multiplicative depth and the bootstrap threshold -/


/-- Conservative noise after `d` multiplication levels when multiplication
squares the current bound. -/
def noiseAfterDepth (B d : ℕ) : ℕ := B ^ (2 ^ d)


/-- A depth is supported exactly when its conservative noise is below the
ciphertext modulus threshold. -/
def SupportsDepth (B T d : ℕ) : Prop := noiseAfterDepth B d < T




end RingLWEFHE

end


