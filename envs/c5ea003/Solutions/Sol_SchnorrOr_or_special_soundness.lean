-- Prove2me | solution 1 for SchnorrOr.or_special_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:04:31.421111+00:00
-- url     : https://prove2.me/submissions/1e92d3e6-7a5c-4e41-afd9-59e18293ae0b

-- Sol generated from Cryptography/ZeroKnowledge/SchnorrOrProof.lean
import Mathlib
import Definitions.Def_Cryptography_SchnorrIdentification
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrOrProof

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

open SchnorrOr

variable (P : SchnorrParams)










/-! ## Honest-verifier zero knowledge via explicit bijections -/








open SchnorrOr in
theorem solution    (Y₁ Y₂ : ZMod P.p) (T T' : OrTranscript P)
    (hT : orAccepts P Y₁ Y₂ T) (hT' : orAccepts P Y₁ Y₂ T')
    (ht₁ : T.t₁ = T'.t₁) (ht₂ : T.t₂ = T'.t₂)
    (hc : T.c ≠ T'.c) :
    ∃ x : ZMod P.p, x * P.g = Y₁ ∨ x * P.g = Y₂ := by
  obtain ⟨hsplit, ha₁, ha₂⟩ := hT
  obtain ⟨hsplit', ha₁', ha₂'⟩ := hT'
  -- distinct overall challenges force a collision in some branch
  have hbranch : T.c₁ ≠ T'.c₁ ∨ T.c₂ ≠ T'.c₂ := by
    by_contra h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    apply hc
    rw [← hsplit, ← hsplit', h1, h2]
  rcases hbranch with h | h
  · -- branch 1 collided: extract a witness for Y₁
    refine ⟨(T.c₁ - T'.c₁)⁻¹ * (T.s₁ - T'.s₁), Or.inl ?_⟩
    have hcne : T.c₁ - T'.c₁ ≠ 0 := sub_ne_zero.mpr h
    have hcancel : (T.s₁ - T'.s₁) * P.g = (T.c₁ - T'.c₁) * (Y₁) := by
      have : (T.s₁ - T'.s₁) * P.g = (T.t₁ + T.c₁ * Y₁) - (T'.t₁ + T'.c₁ * Y₁) := by
        rw [sub_mul, ha₁, ha₁']
      rw [this, ht₁]; ring
    rw [mul_assoc, hcancel, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  · -- branch 2 collided: extract a witness for Y₂
    refine ⟨(T.c₂ - T'.c₂)⁻¹ * (T.s₂ - T'.s₂), Or.inr ?_⟩
    have hcne : T.c₂ - T'.c₂ ≠ 0 := sub_ne_zero.mpr h
    have hcancel : (T.s₂ - T'.s₂) * P.g = (T.c₂ - T'.c₂) * (Y₂) := by
      have : (T.s₂ - T'.s₂) * P.g = (T.t₂ + T.c₂ * Y₂) - (T'.t₂ + T'.c₂ * Y₂) := by
        rw [sub_mul, ha₂, ha₂']
      rw [this, ht₂]; ring
    rw [mul_assoc, hcancel, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
