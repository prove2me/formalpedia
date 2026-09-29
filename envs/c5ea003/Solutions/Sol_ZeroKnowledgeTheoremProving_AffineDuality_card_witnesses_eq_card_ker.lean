-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.AffineDuality.card_witnesses_eq_card_ker
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:13:52.57143+00:00
-- url     : https://prove2.me/submissions/e69262ff-6341-408b-813c-183e34a5f4be

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

/-- Two witnesses for the same statement differ by a kernel element. -/
theorem witness_sub_mem_ker (s : Statement (G := G) (H := H)) {w₁ w₂ : G}
    (h₁ : IsWitness s w₁) (h₂ : IsWitness s w₂) :
    w₁ - w₂ ∈ s.hom.ker := by
  have e₁ : s.hom w₁ = s.target := h₁
  have e₂ : s.hom w₂ = s.target := h₂
  simp [AddMonoidHom.mem_ker, map_sub, e₁, e₂]



/-! ## 3. Soundness amplification over `n` parallel rounds -/


variable (s : Statement (G := G) (H := H)) (n : ℕ)












/-! ## 4. Zero-knowledge proofs of provability -/


variable {Thm Prf : Type*}







open ZeroKnowledgeTheoremProving.AffineDuality in
theorem solution(s : Statement (G := G) (H := H)) {w₀ : G}
    (h₀ : IsWitness s w₀) :
    Nat.card {w : G // IsWitness s w} = Nat.card (s.hom.ker) := by
  have h₀' : s.hom w₀ = s.target := h₀
  have e : {w : G // IsWitness s w} ≃ (s.hom.ker : Set G) :=
    { toFun := fun w => ⟨w.1 - w₀, witness_sub_mem_ker s w.2 h₀⟩
      invFun := fun k => ⟨w₀ + k.1, by
        have hk' : s.hom k.1 = 0 := k.2
        show s.hom (w₀ + k.1) = s.target
        simp [map_add, hk', h₀']⟩
      left_inv := by rintro ⟨w, hw⟩; simp
      right_inv := by rintro ⟨k, hk⟩; simp }
  exact Nat.card_congr e
