-- Prove2me | Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_or_special_soundness
-- name    : ZeroKnowledgeTheoremProving.AffineDuality.or_special_soundness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:09:58.529248+00:00
-- url     : https://prove2.me/theorems/09f7443b-ff04-4f68-8a88-4836497d9b4f
-- title:
--   Soundness of the OR-composition.
-- statement:
--   **Soundness of the OR-composition.** Two accepted conversations sharing both
--   commitments but answering different challenges force one of the two statements
--   to have a witness.
--
--   ```lean
--   theorem ZeroKnowledgeTheoremProving.AffineDuality.or_special_soundness(s₁ s₂ : Statement (G := G) (H := H)) {c c' : Bool}
--       {t t' : OrTranscript G H}
--       (h : OrAccepts s₁ s₂ c t) (h' : OrAccepts s₁ s₂ c' t')
--       (hc₁ : t.commit₁ = t'.commit₁) (hc₂ : t.commit₂ = t'.commit₂)
--       (hcc : c ≠ c') :
--       (∃ w : G, IsWitness s₁ w) ∨ (∃ w : G, IsWitness s₂ w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ZeroKnowledgeTheoremProving/OrComposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ZeroKnowledgeTheoremProving/OrComposition.lean#L153

-- Thm stub generated from Applications/ZeroKnowledgeTheoremProving/OrComposition.lean
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

theorem ZeroKnowledgeTheoremProving.AffineDuality.or_special_soundness(s₁ s₂ : Statement (G := G) (H := H)) {c c' : Bool}
    {t t' : OrTranscript G H}
    (h : OrAccepts s₁ s₂ c t) (h' : OrAccepts s₁ s₂ c' t')
    (hc₁ : t.commit₁ = t'.commit₁) (hc₂ : t.commit₂ = t'.commit₂)
    (hcc : c ≠ c') :
    (∃ w : G, IsWitness s₁ w) ∨ (∃ w : G, IsWitness s₂ w) := by sorry
