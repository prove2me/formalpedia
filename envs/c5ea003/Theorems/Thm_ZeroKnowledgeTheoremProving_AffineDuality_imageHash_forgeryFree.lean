-- Prove2me | Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_imageHash_forgeryFree
-- name    : ZeroKnowledgeTheoremProving.AffineDuality.imageHash_forgeryFree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:09:31.399025+00:00
-- url     : https://prove2.me/theorems/56c0a742-c3ac-4bad-a848-103a854e6de4
-- title:
--   For a false statement the image colouring is forgery-free.
-- statement:
--   For a false statement the image colouring is forgery-free.
--
--   ```lean
--   theorem ZeroKnowledgeTheoremProving.AffineDuality.imageHash_forgeryFree(s : Statement (G := G) (H := H))
--       (hno : ∀ w : G, ¬ IsWitness s w) : ForgeryFree s (imageHash s) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ZeroKnowledgeTheoremProving/FiatShamir.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ZeroKnowledgeTheoremProving/FiatShamir.lean#L141

-- Thm stub generated from Applications/ZeroKnowledgeTheoremProving/FiatShamir.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_FiatShamir

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

open ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]









open scoped Classical in

theorem ZeroKnowledgeTheoremProving.AffineDuality.imageHash_forgeryFree(s : Statement (G := G) (H := H))
    (hno : ∀ w : G, ¬ IsWitness s w) : ForgeryFree s (imageHash s) := by sorry
