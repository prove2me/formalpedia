-- Prove2me | Definitions.Def_Applications_ZeroKnowledgeTheoremProving_FiatShamir
-- name    : Applications_ZeroKnowledgeTheoremProving_FiatShamir
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T01:00:23.093118+00:00
-- url     : https://prove2.me/theorems/3d0dd2d0-6d6d-4a6c-97b9-231e116b30fb
-- title:
--   Aether Catalog definitions — Applications_ZeroKnowledgeTheoremProving_FiatShamir
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ZeroKnowledgeTheoremProving.FiatShamir`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ZeroKnowledgeTheoremProving/FiatShamir.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries

/-!
# The Fiat–Shamir Inversion: Non-Interactive Soundness Holds Exactly for False Statements

Cycle 2 of the research loop. Having proved (in `ProvabilityAmplification`) that
the *interactive* affine Σ-protocol has soundness error `(1/2)^n`, the obvious
next conjecture is that removing interaction — replacing the verifier's coin by
a public hash of the commitment, the Fiat–Shamir transform — preserves
soundness. It does not, and the failure is *unconditional*: it has nothing to do
with the quality of the hash.

Fix a public hash `Hash : H → Bool`. A non-interactive proof is a pair `(a, z)`
accepted when `Accepts s ⟨a, Hash a, z⟩` (`NIZKAccepts`). Call the hash
*forgery-free* for the statement when no such pair exists at all.

The main results are:

* `nizk_exists_iff` — accepted non-interactive proofs correspond exactly to
  solutions of the fixed-point equation `Hash (f z - c · target) = c`;
* `forgeryFree_iff` — forgery-freeness is the conjunction of two rigid colouring
  conditions: `Hash` must be constantly `true` on the image of the public
  homomorphism and constantly `false` on the image translated by `-target`;
* `nizk_exists_of_isWitness` — **if the statement is true, every hash whatsoever
  admits an accepted non-interactive proof**;
* `exists_forgeryFree_iff_no_witness` — **a forgery-free hash exists if and only
  if the statement is false**.

So in the information-theoretic model, a Fiat–Shamir proof of a *true* statement
is never evidence of knowledge: an accepted pair exists unconditionally, for
every hash function. Non-interactive conviction therefore cannot be
information-theoretic; it must rest on the computational hardness of *finding*
the pair. This is the exact boundary of the "prove a theorem without revealing
why" programme: interaction (or computational hardness) is not a convenience but
a necessity, and `zk_convinces_provable` genuinely needs *two* transcripts.

`constantHash_forgeable` records the extreme case: with a constant hash, an
accepted non-interactive proof exists for *every* statement, true or false.
-/

namespace ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- A non-interactive (Fiat–Shamir) proof is a commitment/response pair accepted
when the challenge is the hash of the commitment. -/
def NIZKAccepts (s : Statement (G := G) (H := H)) (Hash : H → Bool) (a : H) (z : G) : Prop :=
  Accepts s ⟨a, Hash a, z⟩



/-- A hash is *forgery-free* for a statement when no non-interactive proof is
accepted. -/
def ForgeryFree (s : Statement (G := G) (H := H)) (Hash : H → Bool) : Prop :=
  ¬ ∃ a z, NIZKAccepts s Hash a z




open scoped Classical in
/-- The canonical candidate: colour the image of the public homomorphism
`true` and everything else `false`. -/
noncomputable def imageHash (s : Statement (G := G) (H := H)) : H → Bool :=
  fun a => decide (∃ z : G, s.hom z = a)




end ZeroKnowledgeTheoremProving.AffineDuality


