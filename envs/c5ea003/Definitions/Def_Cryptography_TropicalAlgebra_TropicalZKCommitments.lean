-- Prove2me | Definitions.Def_Cryptography_TropicalAlgebra_TropicalZKCommitments
-- name    : Cryptography_TropicalAlgebra_TropicalZKCommitments
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:24:57.207956+00:00
-- url     : https://prove2.me/theorems/f05868b5-cc6a-4581-8046-932028a32c28
-- title:
--   Aether Catalog definitions — Cryptography_TropicalAlgebra_TropicalZKCommitments
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.TropicalAlgebra.TropicalZKCommitments`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/TropicalAlgebra/TropicalZKCommitments.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Zero-Knowledge Commitments

This file develops a theory of commitment schemes and zero-knowledge protocols
over the tropical (min-plus) semiring, establishing both impossibility results
for naïve Pedersen-style approaches and constructive alternatives based on
tropical matrix actions.

## Main Results

### Part I: Impossibility (Theorem A)
* `IdempotentSemiring` — class for semirings with `a + a = a`
* `idempotent_semiring_trivial_inverses` — additive inverses force triviality
* `tropical_pedersen_impossible` — linear homomorphic commitments with hiding
  are impossible in idempotent semirings

### Part II: Tropical Matrix Commitments (Theorem B)
* `tropMatVecMul` — tropical matrix-vector product
* `tropCommit` — tropical matrix commitment `C(x, r) = A ⊗ x ⊓ B ⊗ r`
* `tropCommit_binding_of_injective` — binding from injectivity of `A`-action
* `tropMatVecMul_shift_equivariant` — shift equivariance of tropical product

### Part III: Zero-Knowledge by Shift Invariance (Theorem C)
* `TropTranscript` — Σ-protocol transcript type
* `transcript_shift` — global shift action on transcripts
* `transcript_shift_preserves_verification` — shifted transcripts remain valid
* `tropical_sigma_zk` — zero-knowledge: every valid transcript has a
  shifted equivalent that is simulatable

### Part IV: Idempotent Normalization and Composition (Theorem D)
* `normalizeVec` — idempotent normalization (componentwise `⊓`)
* `normalizeVec_idem` — normalization is idempotent
* `compose_transcripts` — sequential composition of transcripts
* `parallel_soundness_decay` — soundness error decays exponentially
  under parallel repetition

## References

* Butkovič, P. "Max-linear Systems: Theory and Algorithms" (2010)
* Grigoriev & Shpilrain "Tropical Cryptography" (2014)
-/

open Finset Function

set_option linter.unusedVariables false

/-! ## Part I: Impossibility of Pedersen-style Commitments in Idempotent Semirings -/

section Impossibility

/-- An idempotent semiring: a semiring where `a + a = a` for all `a`.
    The tropical (min-plus) semiring is the canonical example. -/
class IdempotentSemiring (S : Type*) extends Semiring S where
  add_idem : ∀ a : S, a + a = a





end Impossibility

/-! ## Part II: Tropical Matrix Commitment and Binding -/

section TropicalCommitment

/-- Tropical weight type: natural numbers with infinity (`⊤`). -/
abbrev Trop := WithTop ℕ

/-- Tropical vector. -/
abbrev TropVec (n : ℕ) := Fin n → Trop

/-- Tropical matrix. -/
abbrev TropMat (m n : ℕ) := Matrix (Fin m) (Fin n) Trop

/-- Tropical matrix-vector product: `(A ⊗ x)_i = ⨅_j (A_{i,j} + x_j)`.
    In the min-plus semiring, `+` is the semiring multiplication and `⊓` is
    the semiring addition. -/
noncomputable def tropMatVecMul {m n : ℕ} (A : TropMat m n) (x : TropVec n) : TropVec m :=
  fun i => ⨅ j : Fin n, (A i j + x j)

/-- Tropical matrix commitment: `Com(x, r) = (A ⊗ x) ⊓ (B ⊗ r)`.
    The commitment is the componentwise minimum of two tropical
    matrix-vector products. -/
noncomputable def tropCommit {m n k : ℕ} (A : TropMat m n) (B : TropMat m k)
    (x : TropVec n) (r : TropVec k) : TropVec m :=
  fun i => tropMatVecMul A x i ⊓ tropMatVecMul B r i

/-
**Theorem B: Binding from injectivity of the message encoding.**

    If the tropical matrix-vector product `A ⊗ (·)` is injective on the
    message space, and the commitment values determine the `A`-component
    (i.e. the `B ⊗ r` part doesn't obscure the `A ⊗ x` part), then
    collisions in commitments force message equality.

    This replaces group cancellation with order-theoretic rigidity:
    injectivity of `tropMatVecMul A` is a tropical analogue of
    "full column rank".
-/

/-
Tropical matrix-vector product is shift-equivariant:
    `A ⊗ (x + c) = (A ⊗ x) + c` where `+ c` means adding a constant
    to each component.

    This is the foundation for zero-knowledge: shifting the input
    shifts the output uniformly.
-/

/-
When the `A`-component dominates (is ≤) the `B`-component,
    the commitment equals the `A`-component.
-/

end TropicalCommitment

/-! ## Part III: Zero-Knowledge by Tropical Shift Invariance -/

section ZeroKnowledge

/-- A tropical Σ-protocol transcript: commitment, challenge, response. -/
structure TropTranscript (n : ℕ) (c : ℕ) where
  /-- Commitment vector -/
  com  : TropVec n
  /-- Challenge bits -/
  chal : Fin c → Bool
  /-- Response vector -/
  resp : TropVec n


/-- Shift a tropical vector by adding a constant. -/
def tropShift {n : ℕ} (v : TropVec n) (s : ℕ) : TropVec n :=
  fun i => v i + (s : Trop)

/-- Shift a transcript: add a constant to commitment and response. -/
def transcriptShift {n c : ℕ} (t : TropTranscript n c) (s : ℕ) :
    TropTranscript n c where
  com  := tropShift t.com s
  chal := t.chal
  resp := tropShift t.resp s

/-- A verification predicate for a tropical Σ-protocol. -/
structure TropVerifier (n c : ℕ) where
  /-- The verification check: does the transcript verify? -/
  verify : TropVec n → TropTranscript n c → Bool

/-- A verifier is shift-invariant if shifting the statement and transcript
    together preserves verification. -/
def ShiftInvariantVerifier {n c : ℕ} (V : TropVerifier n c) : Prop :=
  ∀ (stmt : TropVec n) (t : TropTranscript n c) (s : ℕ),
    V.verify stmt t = V.verify (tropShift stmt s) (transcriptShift t s)

/-
**Theorem C (part 1): Shift preserves transcript structure.**
    Shifting a transcript by `s` and then by `t` is the same as
    shifting by `s + t`.
-/

/-
Shifting by zero is the identity.
-/

/-
**Theorem C (part 2): Zero-knowledge by shift invariance.**

    If a verifier is shift-invariant, then for any valid transcript `t`,
    there exists a "simulated" transcript `t'` that is a shifted version
    of `t`. This means the simulator can produce valid-looking transcripts
    by sampling a random shift.

    The key insight: in an idempotent setting, the shift acts as an
    exact algebraic symmetry (not just approximate/statistical), giving
    **perfect** zero-knowledge rather than computational ZK.
-/

end ZeroKnowledge

/-! ## Part IV: Idempotent Normalization and Composition -/

section Composition

/-- Normalize a tropical vector: componentwise application of `⊓` with itself.
    In an idempotent semiring, this is the identity, but it serves as
    the canonical form for composed transcripts. -/
def normalizeVec {n : ℕ} (v : TropVec n) : TropVec n :=
  fun i => v i ⊓ v i

/-
**Theorem D (part 1): Normalization is idempotent.**
    `normalize (normalize v) = normalize v`.
-/

/-
Normalization is the identity on `WithTop ℕ` (since `min` is idempotent).
-/

/-- Compose two transcripts by taking the componentwise minimum
    of their commitments and responses. -/
def composeTranscripts {n c₁ c₂ : ℕ}
    (t₁ : TropTranscript n c₁) (t₂ : TropTranscript n c₂) :
    TropTranscript n (c₁ + c₂) where
  com  := fun i => t₁.com i ⊓ t₂.com i
  chal := fun j => if h : j.val < c₁
    then t₁.chal ⟨j.val, h⟩
    else t₂.chal ⟨j.val - c₁, by omega⟩
  resp := fun i => t₁.resp i ⊓ t₂.resp i


/-
**Theorem D (part 2): Soundness error decays under parallel repetition.**

    If a single-round protocol has soundness error at most `ε` (as a rational),
    meaning a cheating prover convinces the verifier with probability ≤ ε,
    then `k` independent parallel repetitions have soundness error ≤ ε^k.

    This is modeled finitely: if in each round, at most `num` out of `den`
    challenges pass for a cheating prover, then in `k` rounds, at most
    `num^k` out of `den^k` combined challenges pass.
-/

/-
The soundness ratio `num^k / den^k` equals `(num/den)^k`.
-/

end Composition

/-! ## Part V: Connecting the Pieces -/

section Integration

/-
The tropical commitment is monotone in the message:
    if `x₁ ≤ x₂` pointwise, then `Com(x₁, r) ≤ Com(x₂, r)` pointwise.
-/

/-
The tropical matrix-vector product is monotone.
-/

/-
The tropical commitment with a zero randomness vector equals
    the tropical matrix-vector product.
-/

/-
Shift equivariance of the commitment:
    `Com(x + c, r + c) = Com(x, r) + c` when A-component dominates.
-/

end Integration


