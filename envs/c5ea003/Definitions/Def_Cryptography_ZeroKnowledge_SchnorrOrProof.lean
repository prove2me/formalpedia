-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_SchnorrOrProof
-- name    : Cryptography_ZeroKnowledge_SchnorrOrProof
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:30:52.577234+00:00
-- url     : https://prove2.me/theorems/dcdb6142-213d-4051-a51a-6b9dc2ed4ae8
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_SchnorrOrProof
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.SchnorrOrProof`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/SchnorrOrProof.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_SchnorrIdentification

/-!
# Schnorr OR-composition (Cramer–Damgård–Schoenmakers)

This file formalizes the **OR-composition** of two Schnorr Σ-protocols: a proof of
knowledge of a discrete logarithm of *one of two* public keys, without revealing
which one. It extends the catalog's `SchnorrIdentification` (completeness, special
soundness, HVZK of a single Schnorr instance) and `AffineSigmaExtraction` (the
linear-algebra core of extraction).

We work in the same additive model as `SchnorrIdentification`: a prime field
`ZMod P.p` with a fixed nonzero generator `P.g`, where "scalar·group element" is
field multiplication and the public key for secret `x` is `P.pk x = x * P.g`.

## The protocol (proving `∃ x, x·g = Y₁  ∨  x·g = Y₂`)

A transcript is `(t₁, t₂, c, c₁, c₂, s₁, s₂)` and the verifier accepts iff
`c₁ + c₂ = c` and both Schnorr sub-equations `sᵢ·g = tᵢ + cᵢ·Yᵢ` hold.

* The prover who knows a witness for branch `1` runs the *real* Schnorr prover on
  branch `1` (with commitment randomness `r₁`) and *simulates* branch `2` (choosing
  `c₂, s₂` freely and back-solving `t₂`). It then sets `c₁ = c − c₂`.
* The simulator (no witness at all) back-solves *both* commitments.

## Main results

* `orHonest1_accepts` / `orHonest2_accepts` — completeness from either branch.
* `orSim_accepts` — the witness-free simulator always produces accepting transcripts.
* `or_special_soundness` — two accepting transcripts sharing `(t₁, t₂)` with distinct
  overall challenges yield a genuine discrete-log witness for **at least one** of the
  two statements (`∃ x, x·g = Y₁ ∨ x·g = Y₂`).
* `orSimEquiv1` / `orHonest1_eq_sim` — perfect HVZK from branch 1: the honest branch-1
  transcript equals a simulated transcript under an explicit bijection of randomness.
* `orSimEquiv2` / `orHonest2_eq_sim` — perfect HVZK from branch 2.
* `or_witness_indistinguishable` — the branch-1 and branch-2 honest provers, with
  randomness matched through the simulator, produce *identical* transcripts; since the
  simulator is witness-free this is perfect witness indistinguishability.

-- !-- Lab Notes -- !--
Hypothesis (H1): the CDS OR-trick is "just" two affine Schnorr equations glued by the
linear constraint `c₁ + c₂ = c`. Experiment: the special-soundness proof should reduce
to the catalog's 1-D affine extractor applied to whichever branch has a sub-challenge
collision. Outcome: confirmed — the only genuinely new combinatorial content is the
pigeonhole step `c ≠ c' → c₁ ≠ c₁' ∨ c₂ ≠ c₂'`, after which `special_soundness`
(reused from `SchnorrIdentification`) finishes each branch. Insight: OR-composition adds
*no* new algebraic hardness; it is a purely structural lift. Failure analysis: an early
attempt to extract a *named* branch failed (you cannot know which branch collided in
advance); the fix is to return a disjunction, matching the cryptographic guarantee that
the extractor learns *some* witness but not necessarily a chosen one.
-/

namespace SchnorrOr

variable (P : SchnorrParams)

/-- A transcript of the OR-composition: two commitments, the overall challenge, the two
sub-challenges, and the two responses. -/
@[ext]
structure OrTranscript (P : SchnorrParams) where
  t₁ : ZMod P.p
  t₂ : ZMod P.p
  c  : ZMod P.p
  c₁ : ZMod P.p
  c₂ : ZMod P.p
  s₁ : ZMod P.p
  s₂ : ZMod P.p

/-- Verifier acceptance for the OR-composition against public keys `Y₁, Y₂`: the
sub-challenges split the challenge and each Schnorr sub-equation holds. -/
def orAccepts (Y₁ Y₂ : ZMod P.p) (T : OrTranscript P) : Prop :=
  T.c₁ + T.c₂ = T.c ∧
    T.s₁ * P.g = T.t₁ + T.c₁ * Y₁ ∧
    T.s₂ * P.g = T.t₂ + T.c₂ * Y₂

/-- Honest prover that knows a witness `x₁` for branch 1 (`Y₁ = x₁·g`). It runs the
real Schnorr prover on branch 1 with randomness `r₁` and simulates branch 2 with the
freely chosen `(c₂, s₂)`; the overall challenge is `c`. -/
def orHonest1 (x₁ r₁ c₂ s₂ c : ZMod P.p) (Y₂ : ZMod P.p) : OrTranscript P where
  t₁ := r₁ * P.g
  t₂ := s₂ * P.g - c₂ * Y₂
  c  := c
  c₁ := c - c₂
  c₂ := c₂
  s₁ := r₁ + (c - c₂) * x₁
  s₂ := s₂

/-- Honest prover that knows a witness `x₂` for branch 2 (`Y₂ = x₂·g`). It simulates
branch 1 with `(c₁, s₁)` and runs the real Schnorr prover on branch 2 with `r₂`. -/
def orHonest2 (x₂ r₂ c₁ s₁ c : ZMod P.p) (Y₁ : ZMod P.p) : OrTranscript P where
  t₁ := s₁ * P.g - c₁ * Y₁
  t₂ := r₂ * P.g
  c  := c
  c₁ := c₁
  c₂ := c - c₁
  s₁ := s₁
  s₂ := r₂ + (c - c₁) * x₂

/-- The witness-free simulator: choose `c₂, s₁, s₂` and the challenge `c` freely, set
`c₁ = c − c₂`, and back-solve both commitments. -/
def orSim (Y₁ Y₂ c₂ s₁ s₂ c : ZMod P.p) : OrTranscript P where
  t₁ := s₁ * P.g - (c - c₂) * Y₁
  t₂ := s₂ * P.g - c₂ * Y₂
  c  := c
  c₁ := c - c₂
  c₂ := c₂
  s₁ := s₁
  s₂ := s₂





/-! ## Honest-verifier zero knowledge via explicit bijections -/

/-- The bijection underlying HVZK from branch 1: honest branch-1 randomness
`(r₁, c₂, s₂)` maps to simulator randomness `(c₂, s₁, s₂)` with `s₁ = r₁ + (c−c₂)·x₁`. -/
def orSimEquiv1 (x₁ c : ZMod P.p) :
    (ZMod P.p × ZMod P.p × ZMod P.p) ≃ (ZMod P.p × ZMod P.p × ZMod P.p) where
  toFun := fun rcs => (rcs.2.1, rcs.1 + (c - rcs.2.1) * x₁, rcs.2.2)
  invFun := fun cs => (cs.2.1 - (c - cs.1) * x₁, cs.1, cs.2.2)
  left_inv := by rintro ⟨r, c₂, s₂⟩; simp
  right_inv := by rintro ⟨c₂, s₁, s₂⟩; simp


/-- The bijection underlying HVZK from branch 2: honest branch-2 randomness
`(r₂, c₁, s₁)` maps to simulator randomness `(c−c₁, s₁, s₂)`. -/
def orSimEquiv2 (x₂ c : ZMod P.p) :
    (ZMod P.p × ZMod P.p × ZMod P.p) ≃ (ZMod P.p × ZMod P.p × ZMod P.p) where
  toFun := fun rcs => (c - rcs.2.1, rcs.2.2, rcs.1 + (c - rcs.2.1) * x₂)
  invFun := fun cs => (cs.2.2 - cs.1 * x₂, c - cs.1, cs.2.1)
  left_inv := by rintro ⟨r, c₁, s₁⟩; simp
  right_inv := by rintro ⟨c₂, s₁, s₂⟩; simp




end SchnorrOr


