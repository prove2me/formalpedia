-- Prove2me | Definitions.Def_Applications_ZeroKnowledgeTheoremProving_OrComposition
-- name    : Applications_ZeroKnowledgeTheoremProving_OrComposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T01:07:21.398301+00:00
-- url     : https://prove2.me/theorems/918421a3-e0a2-4120-9bc7-6d5fef26c3af
-- title:
--   Aether Catalog definitions — Applications_ZeroKnowledgeTheoremProving_OrComposition
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ZeroKnowledgeTheoremProving.OrComposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ZeroKnowledgeTheoremProving/OrComposition.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_LargeChallengeSpace

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

namespace ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The public conversation of the OR-composed protocol. -/
structure OrTranscript (G H : Type*) where
  commit₁ : H
  commit₂ : H
  chal₁ : Bool
  chal₂ : Bool
  resp₁ : G
  resp₂ : G

/-- The OR-verifier: the sub-challenges must `xor` to the issued challenge and
both sub-conversations must be accepted. -/
def OrAccepts (s₁ s₂ : Statement (G := G) (H := H)) (c : Bool) (t : OrTranscript G H) : Prop :=
  (xor t.chal₁ t.chal₂ = c) ∧
    Accepts s₁ ⟨t.commit₁, t.chal₁, t.resp₁⟩ ∧
    Accepts s₂ ⟨t.commit₂, t.chal₂, t.resp₂⟩

/-- Strategy of a prover who knows a witness `w₁` for the **left** statement:
honest on the left, simulated on the right. The randomness is a tape `r`, a
simulator response `z₂` and the fake right challenge `d`. -/
def orLeft (s₁ s₂ : Statement (G := G) (H := H)) (w₁ : G) (c : Bool)
    (x : G × G × Bool) : OrTranscript G H :=
  ⟨s₁.hom x.1, s₂.hom x.2.1 - challengeTerm x.2.2 s₂.target,
    xor c x.2.2, x.2.2, x.1 + challengeTerm (xor c x.2.2) w₁, x.2.1⟩

/-- Strategy of a prover who knows a witness `w₂` for the **right** statement:
simulated on the left, honest on the right. -/
def orRight (s₁ s₂ : Statement (G := G) (H := H)) (w₂ : G) (c : Bool)
    (y : G × G × Bool) : OrTranscript G H :=
  ⟨s₁.hom y.2.1 - challengeTerm y.2.2 s₁.target, s₂.hom y.1,
    y.2.2, xor c y.2.2, y.2.1, y.1 + challengeTerm (xor c y.2.2) w₂⟩



/-- The reparametrisation of the randomness space that turns the left strategy
into the right strategy. It composes a `xor`-flip of the fake challenge with two
group translations, and is bijective for both reasons at once. -/
def orSwitch (w₁ w₂ : G) (c : Bool) : (G × G × Bool) ≃ (G × G × Bool) where
  toFun x := (x.2.1 - challengeTerm x.2.2 w₂,
    x.1 + challengeTerm (xor c x.2.2) w₁, xor c x.2.2)
  invFun y := (y.2.1 - challengeTerm y.2.2 w₁,
    y.1 + challengeTerm (xor c y.2.2) w₂, xor c y.2.2)
  left_inv x := by
    obtain ⟨r, z, d⟩ := x
    simp only [Prod.mk.injEq]
    refine ⟨by simp, ?_, by cases c <;> cases d <;> rfl⟩
    cases c <;> cases d <;> simp [challengeTerm]
  right_inv y := by
    obtain ⟨r, z, e⟩ := y
    simp only [Prod.mk.injEq]
    refine ⟨by simp, ?_, by cases c <;> cases e <;> rfl⟩
    cases c <;> cases e <;> simp [challengeTerm]




variable {Thm Prf : Type*}


end ZeroKnowledgeTheoremProving.AffineDuality


