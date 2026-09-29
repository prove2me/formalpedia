-- Prove2me | Definitions.Def_Shared_ZeroKnowledge_SnarkSoundness
-- name    : Shared_ZeroKnowledge_SnarkSoundness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:16:20.708396+00:00
-- url     : https://prove2.me/theorems/ccc1a35f-00b8-42ae-b9fe-a6b22e8a2f36
-- title:
--   Aether Catalog definitions — Shared_ZeroKnowledge_SnarkSoundness
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ZeroKnowledge.SnarkSoundness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ZeroKnowledge/SnarkSoundness.lean by skeleton subtraction
import Mathlib

/-!
# A simplified zk-SNARK: R1CS batching, soundness and extraction

Modern succinct arguments (Groth16, Marlin, PLONK, …) all rest on the same two
ingredients, which we isolate and prove here over an arbitrary finite field `F`.

1. **Arithmetization.** A computation is encoded as a rank-1 constraint system
   (`R1CS`): a witness `z : Fin n → F` is valid iff for every constraint `i`
   `⟨Aᵢ, z⟩ * ⟨Bᵢ, z⟩ = ⟨Cᵢ, z⟩`.
2. **Batching / probabilistic checking.** Instead of checking the `m` constraints one by
   one, the verifier sends a single random challenge `r` and checks the equation
   `∑ᵢ errᵢ(z) · rⁱ = 0`, i.e. that the *batching polynomial* `batchPoly` vanishes at
   `r`. This is the polynomial-identity-testing core of every SNARK.

## Main results

* `batchPoly_eq_zero_iff` — the batching polynomial is the zero polynomial exactly when
  the witness satisfies the constraint system (the arithmetization is faithful).
* `batch_completeness` — a valid witness passes the check for every challenge.
* `batch_soundness_card` / `batch_soundness_prob` — an invalid witness passes for at most
  `m - 1` challenges, i.e. with probability at most `(m-1)/|F|` (Schwartz–Zippel).
* `batch_soundness_pow` — `k` independent challenges reduce the error to `((m-1)/|F|)^k`.
* `batch_extraction` — **knowledge soundness in the algebraic model**: if the check
  passes at `m` pairwise distinct challenge points, the witness really is valid.
* `otp_perfect_hiding`, `masked_uniform`, `mask_bijective` — perfect hiding of a
  one-time-pad field mask, the zero-knowledge ingredient: a masked value is uniformly
  distributed, independently of the value being masked.
-/

open Finset Polynomial

namespace ZKSnark

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m n : ℕ}

/-! ## Rank-1 constraint systems -/

/-- A rank-1 constraint system with `m` constraints over `n` variables: three matrices
`A`, `B`, `C`. A witness `z` is valid when `(A z) ⊙ (B z) = C z` entrywise. -/
structure R1CS (F : Type*) (m n : ℕ) where
  /-- Left factor matrix. -/
  A : Fin m → Fin n → F
  /-- Right factor matrix. -/
  B : Fin m → Fin n → F
  /-- Output matrix. -/
  C : Fin m → Fin n → F

/-- The residual of constraint `i` at the assignment `z`. -/
def R1CS.err (S : R1CS F m n) (z : Fin n → F) (i : Fin m) : F :=
  (∑ j, S.A i j * z j) * (∑ j, S.B i j * z j) - (∑ j, S.C i j * z j)

/-- `z` satisfies the constraint system. -/
def R1CS.Satisfies (S : R1CS F m n) (z : Fin n → F) : Prop := ∀ i, S.err z i = 0

instance (S : R1CS F m n) (z : Fin n → F) : Decidable (S.Satisfies z) :=
  decidable_of_iff (∀ i, S.err z i = 0) Iff.rfl

/-! ## The batching polynomial -/

/-- The batching polynomial `∑ᵢ errᵢ(z) · Xⁱ`, whose vanishing at a random point is what
the verifier of the argument system actually checks. -/
noncomputable def batchPoly (S : R1CS F m n) (z : Fin n → F) : Polynomial F :=
  ∑ i : Fin m, C (S.err z i) * X ^ (i : ℕ)





/-! ## Completeness and soundness -/


/-- The set of "bad" challenges: those on which a cheating prover would be believed. -/
noncomputable def badChallenges (S : R1CS F m n) (z : Fin n → F) : Finset F :=
  univ.filter fun r => (batchPoly S z).eval r = 0







/-! ## The zero-knowledge ingredient: perfect hiding of a field mask -/




end ZKSnark


