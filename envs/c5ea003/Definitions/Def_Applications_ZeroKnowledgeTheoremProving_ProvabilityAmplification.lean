-- Prove2me | Definitions.Def_Applications_ZeroKnowledgeTheoremProving_ProvabilityAmplification
-- name    : Applications_ZeroKnowledgeTheoremProving_ProvabilityAmplification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:59:10.108986+00:00
-- url     : https://prove2.me/theorems/abecf922-9488-4f17-9bb8-476432e9f4ab
-- title:
--   Aether Catalog definitions — Applications_ZeroKnowledgeTheoremProving_ProvabilityAmplification
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ZeroKnowledgeTheoremProving.ProvabilityAmplification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ZeroKnowledgeTheoremProving/ProvabilityAmplification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality

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

namespace ZeroKnowledgeTheoremProving.AffineDuality

open Finset

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-! ## 1. Support geometry of the verifier's view -/






/-! ## 2. Kernel-coset structure of the witness set -/




/-! ## 3. Soundness amplification over `n` parallel rounds -/

section Amplification

variable (s : Statement (G := G) (H := H)) (n : ℕ)

/-- A (possibly cheating) prover for the `n`-fold parallel repetition: it fixes
a commitment vector before seeing the challenge, and then may choose its
responses as an arbitrary function of the whole challenge vector. -/
structure ParallelProver (G H : Type*) (n : ℕ) where
  commitments : Fin n → H
  respond : (Fin n → Bool) → (Fin n → G)

/-- The verifier of the parallel repetition accepts iff every round accepts. -/
def ParallelAccepts (P : ParallelProver G H n) (c : Fin n → Bool) : Prop :=
  ∀ i, Accepts s ⟨P.commitments i, c i, P.respond c i⟩


open scoped Classical in
/-- The set of challenge vectors on which the prover succeeds. -/
noncomputable def cheatSet (P : ParallelProver G H n) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun c => ParallelAccepts s n P c)




/-- The honest prover for the parallel repetition: commit to `s.hom (r i)` and
answer with the affine translation of the tape. -/
def honestProver (w : G) (r : Fin n → G) : ParallelProver G H n where
  commitments := fun i => s.hom (r i)
  respond := fun c i => r i + challengeTerm (c i) w



end Amplification

/-! ## 4. Zero-knowledge proofs of provability -/

/-- A formal proof system compiled into the affine Σ-protocol: proofs of the
theorem `thm` are encoded as witnesses of the public group statement `stmt`,
faithfully in both directions. -/
structure ProvabilityCompilation (G H Thm Prf : Type*) [AddCommGroup G] [AddCommGroup H] where
  /-- the public group statement handed to the verifier -/
  stmt : Statement (G := G) (H := H)
  /-- the theorem whose provability is being asserted -/
  thm : Thm
  /-- the proof checker of the underlying formal system -/
  Checks : Thm → Prf → Prop
  /-- encoding of a formal proof as a group witness -/
  encode : Prf → G
  /-- encoded proofs are witnesses -/
  encode_isWitness : ∀ p, Checks thm p → IsWitness stmt (encode p)
  /-- witnesses come from genuine proofs -/
  witness_provable : ∀ w, IsWitness stmt w → ∃ p, Checks thm p

variable {Thm Prf : Type*}






end ZeroKnowledgeTheoremProving.AffineDuality


