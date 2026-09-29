-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.AffineDuality.mem_real_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:17:24.131865+00:00
-- url     : https://prove2.me/submissions/e236c52a-0b9a-4ddb-a1d7-e994fd9cf57b

-- Sol generated from Applications/ZeroKnowledgeTheoremProving/ProvabilityAmplification.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_ProvabilityAmplification

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












/-! ## 4. Zero-knowledge proofs of provability -/


variable {Thm Prf : Type*}







open ZeroKnowledgeTheoremProving.AffineDuality in
theorem solution[Fintype G]
    (s : Statement (G := G) (H := H)) {w : G} (hw : IsWitness s w) (c : Bool)
    (t : Transcript G H) :
    t ∈ Finset.univ.val.map (realTranscript s w · c) ↔
      t.challenge = c ∧ Accepts s t := by
  have hw' : s.hom w = s.target := hw
  constructor
  · intro ht
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp ht
    subst hr
    refine ⟨rfl, ?_⟩
    cases c <;>
      simp [Accepts, realTranscript, challengeTerm, map_add, hw']
  · rintro ⟨hc, hacc⟩
    refine Multiset.mem_map.mpr ⟨t.response - challengeTerm c w, Finset.mem_univ_val _, ?_⟩
    have hcomm : s.hom (t.response - challengeTerm c w) = t.commitment := by
      cases c with
      | false =>
          simp only [challengeTerm, if_neg (Bool.false_ne_true), sub_zero]
          have := hacc
          rw [Accepts, hc] at this
          simpa [challengeTerm] using this
      | true =>
          have hh := hacc
          rw [Accepts, hc] at hh
          simp only [challengeTerm, if_true] at hh ⊢
          rw [map_sub, hw', hh, add_sub_cancel_right]
    have hresp : t.response - challengeTerm c w + challengeTerm c w = t.response := by
      simp
    rw [realTranscript, hcomm, hresp, ← hc]
