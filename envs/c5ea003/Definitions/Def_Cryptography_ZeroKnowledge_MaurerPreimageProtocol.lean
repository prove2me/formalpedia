-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_MaurerPreimageProtocol
-- name    : Cryptography_ZeroKnowledge_MaurerPreimageProtocol
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:30:13.846935+00:00
-- url     : https://prove2.me/theorems/68ebaf90-aefc-484f-b5f3-60f0121d1c8f
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_MaurerPreimageProtocol
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.MaurerPreimageProtocol`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/MaurerPreimageProtocol.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_SchnorrIdentification

/-!
# Maurer's unified "preimage of a group homomorphism" Σ-protocol

Schnorr identification, Chaum–Pedersen, Okamoto, Guillou–Quisquater and many other
Σ-protocols are all special cases of a single abstract protocol, identified by Ueli Maurer:
a *proof of knowledge of a preimage of a group homomorphism* `φ`. This file formalizes
that unification in two regimes and connects it back to the catalog's
`SchnorrIdentification`.

Given a homomorphism `φ : A → B` of additive abelian groups and a public value `Y = φ x`,
the protocol is:

* commitment `t = φ r` for random `r`;
* challenge `c`;
* response `s = r + c • x`;
* verifier accepts iff `φ s = t + c • Y`.

## Two regimes

* **Known-order / field regime** (`section FieldRegime`): challenges live in a field `F`
  and `A, B` are `F`-modules with `φ` `F`-linear. Two accepting transcripts with distinct
  challenges recover `x = (c₁ − c₂)⁻¹ • (s₁ − s₂)` directly. This subsumes Schnorr,
  Okamoto and the affine-matrix extractor of `AffineSigmaExtraction`.
* **Hidden-order / integer regime** (`section HiddenOrderRegime`): challenges are integers,
  `A, B` are arbitrary additive abelian groups, and extraction succeeds whenever a *special
  preimage* `φ u = ℓ • Y` is known with `IsCoprime ℓ (c₁ − c₂)`. Via Bézout, the witness is
  `x = a • u + b • (s₁ − s₂)`. This is the regime of groups of unknown order (RSA,
  class groups, Guillou–Quisquater) where no field inverse of the challenge difference
  exists — it cannot be reached by the linear-algebra extractor.

## Main results

* `FieldRegime.completeness`, `FieldRegime.special_soundness`,
  `FieldRegime.honest_eq_sim` (perfect HVZK bijection).
* `HiddenOrder.completeness`, `HiddenOrder.special_soundness_coprime`.
* `schnorr_completeness_via_maurer`, `schnorr_special_soundness_via_maurer` — the catalog's
  Schnorr statements recovered as instances of the field regime.

-- !-- Lab Notes -- !--
Hypothesis (H2): every "linear" Σ-protocol extractor in the catalog is one instance of a
single homomorphism-preimage extractor, and the *field* assumption is not essential — only
an inverse of the challenge difference is. Experiment: replace the field inverse by a
Bézout combination using a known multiple `ℓ • Y` of the statement. Outcome: the integer
regime (`special_soundness_coprime`) proves extraction with **no division at all**, purely
from `IsCoprime ℓ (c₁ − c₂)` and `map_zsmul`. Insight: the catalog's `affineExtract1D`
(needing `(c₁−c₂)⁻¹`) is the *field specialization* `ℓ = 1, u = x` of the integer
extractor where coprimality degenerates to invertibility. Failure analysis: a first attempt
stated the integer extractor with `Nat.gcd ℓ d = 1`; converting to Bézout coefficients was
awkward, so we switched to Mathlib's `IsCoprime` which packages the Bézout identity
`a*ℓ + b*d = 1` directly and made the proof a two-line `map`/`zsmul` computation.
-/

namespace MaurerPreimage

/-! ## Field / known-order regime -/

namespace FieldRegime

variable {F : Type*} [Field F]
variable {A B : Type*} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
variable (φ : A →ₗ[F] B)

/-- Acceptance predicate: `φ s = t + c • Y`. -/
def Accepts (Y t : B) (c : F) (s : A) : Prop := φ s = t + c • Y



/-- The simulator: choose challenge `c` and response `s` freely, back-solve the commitment
`t = φ s − c • Y`. -/
def simCommit (Y : B) (c : F) (s : A) : B := φ s - c • Y




end FieldRegime

/-! ## Hidden-order / integer-challenge regime -/

namespace HiddenOrder

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable (φ : A →+ B)

/-- Acceptance predicate with integer challenges: `φ s = t + c • Y`. -/
def ZAccepts (Y t : B) (c : ℤ) (s : A) : Prop := φ s = t + c • Y



end HiddenOrder

/-! ## Schnorr as an instance of the field regime

We recover the catalog's Schnorr completeness and special-soundness statements
(`SchnorrParams`, `accepts`) from `FieldRegime`, with `φ` the `ZMod p`-linear map
`x ↦ x * g`. -/

/-- The Schnorr homomorphism `x ↦ x * g` as a `ZMod p`-linear map. -/
def schnorrHom (P : SchnorrParams) : ZMod P.p →ₗ[ZMod P.p] ZMod P.p where
  toFun := fun x => x * P.g
  map_add' := by intro a b; ring
  map_smul' := by intro a b; simp [smul_eq_mul]; ring




end MaurerPreimage


