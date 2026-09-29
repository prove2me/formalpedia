-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.AffineDuality.soundness_error_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:31:29.453771+00:00
-- url     : https://prove2.me/submissions/bef5b5bc-e420-4363-b42b-9fd1c741c68c

-- Sol generated from Applications/ZeroKnowledgeTheoremProving/ProvabilityAmplification.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_ProvabilityAmplification
import Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_parallel_unique_of_no_witness

/-!
# Zero-Knowledge Provability: Amplification, Support Geometry and Proof Transfer

This file continues the affine Σ-protocol theory of
`Applications.ZeroKnowledgeTheoremProving.AffineDuality`, where the two
directions of one affine law were shown to give *privacy* (translating a random
tape by the witness is a measure-preserving permutation) and *extraction*
(subtracting two accepting responses at one commitment recovers a witness).

Here we push that duality into three genuinely new layers.

1. **Support geometry.** The real execution of the protocol does not merely have
   the same multiset of transcripts as the simulator; that common multiset is
   *exactly* the set of accepting transcripts with the given challenge, each
   occurring with multiplicity one (`real_support_eq_accepting`,
   `real_count_le_one`). So the verifier's view is a *uniform* distribution on
   a set defined by the public verification equation alone.

2. **Soundness amplification (counting).** If the public statement has no
   witness, then for any fixed commitment vector a cheating prover can answer at
   *most one* challenge vector out of `2 ^ n` (`cheatSet_card_le_one`), giving a
   quantitative soundness error `≤ (1/2)^n` (`soundness_error_le`), while an
   honest prover holding a witness answers *all* `2 ^ n` of them
   (`honest_cheatSet_eq_univ`). The resulting dichotomy
   (`amplified_soundness_dichotomy`) is exponentially sharp: the accepting set
   jumps from cardinality `≤ 1` to cardinality `2 ^ n`.

3. **Provability transfer.** Packaging a formal proof system (a checking
   relation `Checks : Thm → Prf → Prop`) into the group-theoretic statement via
   an encoding turns the Σ-protocol into a zero-knowledge proof *of provability*:
   the verifier becomes convinced that `∃ p, Checks T p` (`zk_convinces_provable`)
   although its entire view is produced by a simulator that never sees a proof,
   and is literally identical for any two proofs of `T`
   (`zk_provability_transfer`).

The cross-domain bridge is: a finite abelian group acting by translation
(algebra) controls a counting/measure statement on transcript multisets
(combinatorics/probability), which in turn certifies a purely logical statement
about a proof system (logic).
-/

open ZeroKnowledgeTheoremProving.AffineDuality

open Finset

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-! ## 1. Support geometry of the verifier's view -/






/-! ## 2. Kernel-coset structure of the witness set -/




/-! ## 3. Soundness amplification over `n` parallel rounds -/


variable (s : Statement (G := G) (H := H)) (n : ℕ)





open scoped Classical in
/-- Without a witness, the cheating set has at most one element out of `2 ^ n`. -/
theorem cheatSet_card_le_one (hno : ∀ w : G, ¬ IsWitness s w)
    (P : ParallelProver G H n) :
    (cheatSet s n P).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [cheatSet, Finset.mem_filter] at ha hb
  exact parallel_unique_of_no_witness s n hno P ha.2 hb.2

/-- The total number of challenge vectors is `2 ^ n`. -/
theorem card_challenge_vectors :
    (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
  simp






/-! ## 4. Zero-knowledge proofs of provability -/


variable {Thm Prf : Type*}







open ZeroKnowledgeTheoremProving.AffineDuality in
open scoped Classical in
theorem solution(hno : ∀ w : G, ¬ IsWitness s w)
    (P : ParallelProver G H n) :
    ((cheatSet s n P).card : ℚ) / (Finset.univ : Finset (Fin n → Bool)).card
      ≤ (1 / 2) ^ n := by
  rw [card_challenge_vectors n]
  have h2 : (0 : ℚ) < 2 ^ n := by positivity
  rw [div_le_iff₀ (by exact_mod_cast h2)]
  have hcard : ((cheatSet s n P).card : ℚ) ≤ 1 := by
    exact_mod_cast cheatSet_card_le_one s n hno P
  calc ((cheatSet s n P).card : ℚ) ≤ 1 := hcard
    _ = (1 / 2 : ℚ) ^ n * 2 ^ n := by
        rw [div_pow, one_pow, div_mul_cancel₀]
        exact ne_of_gt h2
    _ = (1 / 2 : ℚ) ^ n * ((2 ^ n : ℕ) : ℚ) := by push_cast; ring
