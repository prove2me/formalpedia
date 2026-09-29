-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.AffineDuality.accepting_ncard_eq_card_group
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:13:52.03952+00:00
-- url     : https://prove2.me/submissions/c3f17d18-ff42-41d6-806d-10bdfe692800

-- Sol generated from Applications/ZeroKnowledgeTheoremProving/EntropyAndBoundaries.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_ProvabilityAmplification
import Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_accepting_eq_range_simulator
import Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_simulatedTranscript_injective

/-!
# Entropy of the Verifier's View and the Boundaries of Zero-Knowledge Provability

This file is the adversarial-review layer of the affine Σ-protocol development
(`AffineDuality`, `ProvabilityAmplification`). It answers three questions that
the earlier files raised but did not settle.

## 1. How much randomness does the verifier see?

`accepting_eq_range_simulator` shows that, for a fixed challenge, the set of
accepting transcripts is *exactly* the range of the simulator — with no
assumption that the statement is even true. Combined with injectivity of the
simulator this yields `accepting_ncard_eq_card_group`: the verifier's view is
uniform on a set of size `|G|`, i.e. it carries exactly `log₂ |G|` bits, all of
them coming from the prover's tape and none from the witness. This is a
quantitative form of "zero knowledge": the *size* of the view does not depend on
the statement, the target, or the witness.

## 2. Does privacy need many witnesses?

Folklore says a Σ-protocol hides its witness because many witnesses are
consistent with the public statement. `unique_witness_still_perfect_zk` refutes
this in the sharpest possible way: when `ker s.hom` is trivial the witness is
*unique* (`card_witnesses_eq_one_of_trivial_ker`) and yet the verifier's view is
still exactly the simulator's. Privacy comes from translation symmetry of the
tape space, not from ambiguity of the witness.

## 3. Where does conviction actually come from?

`compilationOfProof` shows that any *provable* theorem can be compiled into the
affine protocol. Its mirror image, `unprovable_no_double_answer`, shows that for
an unprovable theorem no commitment ever admits accepting answers to both
challenges; together with `unprovable_soundness_error` this delimits exactly
what the verifier learns. Finally `zero_hom_compilation_is_vacuous` is a
deliberately negative result: the zero homomorphism yields a compilation whose
extraction step is content-free, so faithfulness of the encoding — not the
protocol — is the load-bearing assumption.
-/

open ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-! ## 1. The accepting set is the simulator's range -/




/-! ## 2. Privacy does not come from witness ambiguity -/



/-! ## 3. Where conviction comes from -/

variable {Thm Prf : Type*}








open ZeroKnowledgeTheoremProving.AffineDuality in
theorem solution[Fintype G]
    (s : Statement (G := G) (H := H)) (c : Bool) :
    {t : Transcript G H | t.challenge = c ∧ Accepts s t}.ncard = Fintype.card G := by
  rw [accepting_eq_range_simulator s c,
    Set.ncard_range_of_injective (simulatedTranscript_injective s c),
    Nat.card_eq_fintype_card]
