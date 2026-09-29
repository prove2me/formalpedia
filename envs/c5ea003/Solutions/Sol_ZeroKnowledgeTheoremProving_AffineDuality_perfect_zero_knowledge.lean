-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.AffineDuality.perfect_zero_knowledge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:19:12.066514+00:00
-- url     : https://prove2.me/submissions/6c217bc2-82cb-4c42-8db9-388621382bd6

-- Sol generated from Applications/ZeroKnowledgeTheoremProving/AffineDuality.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality

/-!
# Affine Duality: Translation Hides Witnesses, Subtraction Extracts Them

This file connects two apparently opposed ideas:

* **finite-group symmetry:** translation permutes a random-tape space without
  changing its uniform distribution;
* **cryptographic proof of knowledge:** two accepting answers to opposite
  challenges determine a witness by subtraction.

These are the two directions of one affine law. Translating a random tape by the
witness gives an exact simulator (privacy), while subtracting two translated
responses recovers the witness (knowledge soundness).

The main theorem `affine_privacy_extraction_duality` says simultaneously that
any two witnesses for the same public statement produce exactly the same
multiset of public transcripts, and that accepting responses to both Boolean
challenges at one commitment reveal a witness. Privacy and extraction coexist:
privacy concerns one randomized transcript, whereas extraction compares two
correlated transcripts having the same commitment.
-/

open ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]










/-- A real transcript is pointwise equal to a simulator transcript after the
measure-preserving affine reindexing of random tapes. -/
theorem real_eq_simulated_reindexed
    (s : Statement (G := G) (H := H)) {w : G} (hw : IsWitness s w)
    (r : G) (c : Bool) :
    realTranscript s w r c = simulatedTranscript s (tapeEquiv c w r) c := by
  unfold tapeEquiv
  cases c <;> simp [realTranscript, simulatedTranscript, challengeTerm]
  rw [hw, add_sub_cancel_right]







open ZeroKnowledgeTheoremProving.AffineDuality in
theorem solution[Fintype G]
    (s : Statement (G := G) (H := H)) {w : G} (hw : IsWitness s w) (c : Bool) :
    (Finset.univ.val.map (realTranscript s w · c)) =
      (Finset.univ.val.map (simulatedTranscript s · c)) := by
  have hbij : Multiset.map (fun x => tapeEquiv c w x) Finset.univ.val =
      Finset.univ.val := Multiset.map_univ_val_equiv (tapeEquiv c w)
  simp [real_eq_simulated_reindexed s hw]
  conv_rhs => rw [← hbij, Multiset.map_map]
  rfl
