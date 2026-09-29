-- Prove2me | Definitions.Def_Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries
-- name    : Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:59:42.917299+00:00
-- url     : https://prove2.me/theorems/d2eb3e1e-9340-4195-95a4-f49b09e542e9
-- title:
--   Aether Catalog definitions — Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ZeroKnowledgeTheoremProving.EntropyAndBoundaries`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ZeroKnowledgeTheoremProving/EntropyAndBoundaries.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
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

namespace ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-! ## 1. The accepting set is the simulator's range -/




/-! ## 2. Privacy does not come from witness ambiguity -/



/-! ## 3. Where conviction comes from -/

variable {Thm Prf : Type*}

/-- Compiling a *provable* theorem: fix one checking proof `p₀`, publish the
image of its encoding, and assume the encoding sends all checking proofs to the
same public target (this is the faithfulness assumption of the compiler). -/
def compilationOfProof (hom : G →+ H) (encode : Prf → G) (T : Thm)
    (Checks : Thm → Prf → Prop) {p₀ : Prf} (hp₀ : Checks T p₀)
    (hcorr : ∀ p, Checks T p → hom (encode p) = hom (encode p₀)) :
    ProvabilityCompilation G H Thm Prf where
  stmt := ⟨hom, hom (encode p₀)⟩
  thm := T
  Checks := Checks
  encode := encode
  encode_isWitness := fun p hp => hcorr p hp
  witness_provable := fun _ _ => ⟨p₀, hp₀⟩






end ZeroKnowledgeTheoremProving.AffineDuality


