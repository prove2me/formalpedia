-- Prove2me | Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_accepting_eq_range_simulator
-- name    : ZeroKnowledgeTheoremProving.AffineDuality.accepting_eq_range_simulator
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:08:56.768579+00:00
-- url     : https://prove2.me/theorems/5b4533e4-4118-4882-848f-57ae2c2bad20
-- title:
--   Statement-independent geometry of acceptance.
-- statement:
--   **Statement-independent geometry of acceptance.** For a fixed challenge the
--   accepting transcripts are precisely the simulator's outputs. No witness, and no
--   truth of the statement, is needed.
--
--   ```lean
--   theorem ZeroKnowledgeTheoremProving.AffineDuality.accepting_eq_range_simulator(s : Statement (G := G) (H := H)) (c : Bool) :
--       {t : Transcript G H | t.challenge = c ∧ Accepts s t} =
--         Set.range (fun z : G => simulatedTranscript s z c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ZeroKnowledgeTheoremProving/EntropyAndBoundaries.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ZeroKnowledgeTheoremProving/EntropyAndBoundaries.lean#L47

-- Thm stub generated from Applications/ZeroKnowledgeTheoremProving/EntropyAndBoundaries.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_ProvabilityAmplification

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

theorem ZeroKnowledgeTheoremProving.AffineDuality.accepting_eq_range_simulator(s : Statement (G := G) (H := H)) (c : Bool) :
    {t : Transcript G H | t.challenge = c ∧ Accepts s t} =
      Set.range (fun z : G => simulatedTranscript s z c) := by sorry
