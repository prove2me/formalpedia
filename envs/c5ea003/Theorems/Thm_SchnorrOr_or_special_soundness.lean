-- Prove2me | Theorems.Thm_SchnorrOr_or_special_soundness
-- name    : SchnorrOr.or_special_soundness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:00:23.056629+00:00
-- url     : https://prove2.me/theorems/f77c069a-58b7-4678-a789-1cebbf75de35
-- title:
--   Special soundness of the OR-composition.
-- statement:
--   **Special soundness of the OR-composition.** Two accepting transcripts sharing the
--   same commitments `(t₁, t₂)` but with distinct overall challenges allow extraction of a
--   genuine discrete-log witness for **at least one** of the two statements.
--
--   ```lean
--   theorem SchnorrOr.or_special_soundness    (Y₁ Y₂ : ZMod P.p) (T T' : OrTranscript P)
--       (hT : orAccepts P Y₁ Y₂ T) (hT' : orAccepts P Y₁ Y₂ T')
--       (ht₁ : T.t₁ = T'.t₁) (ht₂ : T.t₂ = T'.t₂)
--       (hc : T.c ≠ T'.c) :
--       ∃ x : ZMod P.p, x * P.g = Y₁ ∨ x * P.g = Y₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ZeroKnowledge/SchnorrOrProof.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ZeroKnowledge/SchnorrOrProof.lean#L130

-- Thm stub generated from Cryptography/ZeroKnowledge/SchnorrOrProof.lean
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

theorem SchnorrOr.or_special_soundness    (Y₁ Y₂ : ZMod P.p) (T T' : OrTranscript P)
    (hT : orAccepts P Y₁ Y₂ T) (hT' : orAccepts P Y₁ Y₂ T')
    (ht₁ : T.t₁ = T'.t₁) (ht₂ : T.t₂ = T'.t₂)
    (hc : T.c ≠ T'.c) :
    ∃ x : ZMod P.p, x * P.g = Y₁ ∨ x * P.g = Y₂ := by sorry
