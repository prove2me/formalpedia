-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.AffineDuality.or_special_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:19:11.118772+00:00
-- url     : https://prove2.me/submissions/71695598-014f-4f28-97f5-36b14fbdf29a

-- Sol generated from Applications/ZeroKnowledgeTheoremProving/OrComposition.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_LargeChallengeSpace
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_OrComposition
import Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_special_soundness

/-!
# Cycle 4: OR-Composition — Which Theorem Do You Know How To Prove?

The slogan "I can prove Fermat's Last Theorem without revealing why" has a
sharper cousin: *I can prove that at least one of two theorems is provable
without revealing which one I can prove.* This file formalises the classical
OR-composition (Cramer–Damgård–Schoenmakers style) of the affine Σ-protocol of
`AffineDuality` and proves both of its defining properties.

The prover publishes two commitments and, on receiving the challenge `c`, two
sub-challenges `c₁, c₂` with `c₁ xor c₂ = c` together with accepting responses
for both statements. Knowing a witness for the *left* statement it runs the
honest protocol on the left and the simulator on the right; knowing a witness
for the *right* statement it does the mirror image.

* `orLeft_accepts` / `orRight_accepts` — both strategies always produce accepted
  conversations (completeness).
* `orSwitch` and `orLeft_eq_orRight_switch` — an explicit bijection of the
  randomness space `G × G × Bool` carrying the left strategy pointwise onto the
  right strategy. This is the heart of the matter: the two strategies are
  reparametrisations of each other.
* `or_witness_side_hiding` — consequently the two strategies induce *literally
  the same multiset* of transcripts. The verifier's view does not contain the
  information of which of the two statements the prover can prove.
* `or_special_soundness` — two accepted conversations with the same pair of
  commitments and different overall challenges force a witness for one of the
  two statements to exist.
* `or_provability_transfer` — the statement in the language of compiled formal
  systems: the verifier is convinced that `T₁` or `T₂` is provable, while its
  view is the same whether the prover holds a proof of `T₁` or of `T₂`.

The bridge here is between a bit-level combinatorial gadget (splitting a
challenge by `xor`) and the group-translation symmetry that gave privacy in
cycle 1: the composite bijection mixes the two, and each factor is invertible
for a different reason.
-/

open ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]











variable {Thm Prf : Type*}



open ZeroKnowledgeTheoremProving.AffineDuality in
theorem solution(s₁ s₂ : Statement (G := G) (H := H)) {c c' : Bool}
    {t t' : OrTranscript G H}
    (h : OrAccepts s₁ s₂ c t) (h' : OrAccepts s₁ s₂ c' t')
    (hc₁ : t.commit₁ = t'.commit₁) (hc₂ : t.commit₂ = t'.commit₂)
    (hcc : c ≠ c') :
    (∃ w : G, IsWitness s₁ w) ∨ (∃ w : G, IsWitness s₂ w) := by
  obtain ⟨hx, ha₁, ha₂⟩ := h
  obtain ⟨hx', ha₁', ha₂'⟩ := h'
  -- the sub-challenges cannot agree in both coordinates
  have hdiff : t.chal₁ ≠ t'.chal₁ ∨ t.chal₂ ≠ t'.chal₂ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨e₁, e₂⟩ := hcon
    exact hcc (by rw [← hx, ← hx', e₁, e₂])
  rcases hdiff with hne | hne
  · left
    cases hb : t.chal₁ <;> cases hb' : t'.chal₁
    · exact absurd (hb.trans hb'.symm) hne
    · rw [hb] at ha₁
      rw [hb', ← hc₁] at ha₁'
      exact ⟨_, special_soundness s₁ t.commit₁ t.resp₁ t'.resp₁ ha₁ ha₁'⟩
    · rw [hb] at ha₁
      rw [hb', ← hc₁] at ha₁'
      exact ⟨_, special_soundness s₁ t.commit₁ t'.resp₁ t.resp₁ ha₁' ha₁⟩
    · exact absurd (hb.trans hb'.symm) hne
  · right
    cases hb : t.chal₂ <;> cases hb' : t'.chal₂
    · exact absurd (hb.trans hb'.symm) hne
    · rw [hb] at ha₂
      rw [hb', ← hc₂] at ha₂'
      exact ⟨_, special_soundness s₂ t.commit₂ t.resp₂ t'.resp₂ ha₂ ha₂'⟩
    · rw [hb] at ha₂
      rw [hb', ← hc₂] at ha₂'
      exact ⟨_, special_soundness s₂ t.commit₂ t'.resp₂ t.resp₂ ha₂' ha₂⟩
    · exact absurd (hb.trans hb'.symm) hne
