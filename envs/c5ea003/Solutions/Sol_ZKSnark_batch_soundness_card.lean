-- Prove2me | solution 1 for ZKSnark.batch_soundness_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:11:48.364233+00:00
-- url     : https://prove2.me/submissions/1a6d80f9-4dba-4a97-a372-92224976e59b

-- Sol generated from Shared/ZeroKnowledge/SnarkSoundness.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_SnarkSoundness

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


omit [Fintype F] [DecidableEq F] in
/-- The coefficients of the batching polynomial are exactly the constraint residuals. -/
theorem batchPoly_coeff (S : R1CS F m n) (z : Fin n → F) (i : Fin m) :
    (batchPoly S z).coeff (i : ℕ) = S.err z i := by
  simp [batchPoly, Polynomial.finset_sum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj]

omit [Fintype F] [DecidableEq F] in
/-- The batching polynomial has degree at most `m - 1`. -/
theorem batchPoly_natDegree_le (S : R1CS F m n) (z : Fin n → F) :
    (batchPoly S z).natDegree ≤ m - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (natDegree_C_mul_le _ _) ?_
  have hi := i.isLt
  simp only [natDegree_X_pow]
  omega


omit [Fintype F] [DecidableEq F] in
/-- Faithfulness of the arithmetization: the batching polynomial vanishes identically iff
the witness satisfies every constraint. -/
theorem batchPoly_eq_zero_iff (S : R1CS F m n) (z : Fin n → F) :
    batchPoly S z = 0 ↔ S.Satisfies z := by
  constructor
  · intro h i
    have := batchPoly_coeff S z i
    rw [h] at this
    simpa using this.symm
  · intro h
    unfold batchPoly
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h i]
    simp

/-! ## Completeness and soundness -/



/-- Bad challenges are roots of the (then nonzero) batching polynomial. -/
theorem badChallenges_subset_roots (S : R1CS F m n) (z : Fin n → F)
    (h : ¬ S.Satisfies z) : badChallenges S z ⊆ (batchPoly S z).roots.toFinset := by
  have hne : batchPoly S z ≠ 0 := fun hz => h ((batchPoly_eq_zero_iff S z).mp hz)
  intro r hr
  simp only [badChallenges, mem_filter, mem_univ, true_and] at hr
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
  exact hr






/-! ## The zero-knowledge ingredient: perfect hiding of a field mask -/





open ZKSnark in
theorem solution(S : R1CS F m n) (z : Fin n → F) (h : ¬ S.Satisfies z) :
    (badChallenges S z).card ≤ m - 1 := by
  have hne : batchPoly S z ≠ 0 := fun hz => h ((batchPoly_eq_zero_iff S z).mp hz)
  have hroots : (batchPoly S z).roots.card ≤ (batchPoly S z).natDegree := by
    have hc := Polynomial.card_roots hne
    rw [Polynomial.degree_eq_natDegree hne] at hc
    exact WithBot.coe_le_coe.mp hc
  calc (badChallenges S z).card
      ≤ (batchPoly S z).roots.toFinset.card :=
        card_le_card (badChallenges_subset_roots S z h)
    _ ≤ (batchPoly S z).roots.card := Multiset.toFinset_card_le _
    _ ≤ (batchPoly S z).natDegree := hroots
    _ ≤ m - 1 := batchPoly_natDegree_le S z
