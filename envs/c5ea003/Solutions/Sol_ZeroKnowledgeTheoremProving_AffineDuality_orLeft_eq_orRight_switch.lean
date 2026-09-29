-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.AffineDuality.orLeft_eq_orRight_switch
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:17:25.077748+00:00
-- url     : https://prove2.me/submissions/9b475b32-ded9-4277-8dba-f75bc4f7977f

-- Sol generated from Applications/ZeroKnowledgeTheoremProving/OrComposition.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_LargeChallengeSpace
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_OrComposition

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
theorem solution(s₁ s₂ : Statement (G := G) (H := H))
    {w₁ w₂ : G} (hw₁ : IsWitness s₁ w₁) (hw₂ : IsWitness s₂ w₂) (c : Bool)
    (x : G × G × Bool) :
    orLeft s₁ s₂ w₁ c x = orRight s₁ s₂ w₂ c (orSwitch w₁ w₂ c x) := by
  have h₁ : s₁.hom w₁ = s₁.target := hw₁
  have h₂ : s₂.hom w₂ = s₂.target := hw₂
  obtain ⟨r, z, d⟩ := x
  have e₁ : s₁.hom (r + challengeTerm (xor c d) w₁) - challengeTerm (xor c d) s₁.target
      = s₁.hom r := by
    cases hb : xor c d <;> simp [challengeTerm, map_add, h₁]
  have e₂ : s₂.hom (z - challengeTerm d w₂) = s₂.hom z - challengeTerm d s₂.target := by
    cases hb : d <;> simp [challengeTerm, map_sub, h₂]
  have e₃ : z - challengeTerm d w₂ + challengeTerm (xor c (xor c d)) w₂ = z := by
    cases c <;> cases d <;> simp [challengeTerm]
  show (⟨s₁.hom r, s₂.hom z - challengeTerm d s₂.target, xor c d, d,
      r + challengeTerm (xor c d) w₁, z⟩ : OrTranscript G H) = _
  unfold orRight orSwitch
  simp only [Equiv.coe_fn_mk]
  rw [OrTranscript.mk.injEq]
  refine ⟨e₁.symm, e₂.symm, rfl, ?_, rfl, e₃.symm⟩
  cases c <;> cases d <;> rfl
