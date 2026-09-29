-- Prove2me | Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_simulatedTranscript_injective
-- name    : ZeroKnowledgeTheoremProving.AffineDuality.simulatedTranscript_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:09:00.232299+00:00
-- url     : https://prove2.me/theorems/0167983b-6322-4f7d-8098-a9bf768b9007
-- title:
--   The simulator's transcript map is injective in the chosen response.
-- statement:
--   The simulator's transcript map is injective in the chosen response.
--
--   ```lean
--   theorem ZeroKnowledgeTheoremProving.AffineDuality.simulatedTranscript_injective(s : Statement (G := G) (H := H)) (c : Bool) :
--       Function.Injective (fun z : G => simulatedTranscript s z c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ZeroKnowledgeTheoremProving/ProvabilityAmplification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ZeroKnowledgeTheoremProving/ProvabilityAmplification.lean#L60

-- Thm stub generated from Applications/ZeroKnowledgeTheoremProving/ProvabilityAmplification.lean
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

theorem ZeroKnowledgeTheoremProving.AffineDuality.simulatedTranscript_injective(s : Statement (G := G) (H := H)) (c : Bool) :
    Function.Injective (fun z : G => simulatedTranscript s z c) := by sorry
