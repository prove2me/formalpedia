-- Prove2me | solution 1 for ZKSnark.batch_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:13:16.940677+00:00
-- url     : https://prove2.me/submissions/0693c152-2524-4040-99b9-60057670c817

-- Sol generated from Shared/ZeroKnowledge/SnarkSoundness.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_SnarkSoundness
import Theorems.Thm_ZKSnark_batch_soundness_card

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

open ZKSnark

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m n : ℕ}

/-! ## Rank-1 constraint systems -/





/-! ## The batching polynomial -/






/-! ## Completeness and soundness -/









/-! ## The zero-knowledge ingredient: perfect hiding of a field mask -/





open ZKSnark in
theorem solution(S : R1CS F m n) (z : Fin n → F) (T : Finset F) (hT : m ≤ T.card)
    (h : ∀ r ∈ T, (batchPoly S z).eval r = 0) : S.Satisfies z := by
  by_contra hcon
  have hsub : T ⊆ badChallenges S z := by
    intro r hr
    simp only [badChallenges, mem_filter, mem_univ, true_and]
    exact h r hr
  have h1 : T.card ≤ m - 1 := le_trans (card_le_card hsub) (batch_soundness_card S z hcon)
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      exact absurd (fun i : Fin 0 => i.elim0) hcon
    · exact hm0
  omega
