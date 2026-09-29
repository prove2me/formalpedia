-- Prove2me | Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_special_soundness
-- name    : ZeroKnowledgeTheoremProving.AffineDuality.special_soundness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:09:42.983187+00:00
-- url     : https://prove2.me/theorems/ef8b7574-5541-4b16-8a69-a3e1f4340ad6
-- title:
--   Two accepting answers to opposite challenges at one commitment extract a
-- statement:
--   Two accepting answers to opposite challenges at one commitment extract a
--   witness by subtraction.
--
--   ```lean
--   theorem ZeroKnowledgeTheoremProving.AffineDuality.special_soundness(s : Statement (G := G) (H := H))
--       (a : H) (zFalse zTrue : G)
--       (hFalse : Accepts s ⟨a, false, zFalse⟩)
--       (hTrue : Accepts s ⟨a, true, zTrue⟩) :
--       IsWitness s (zTrue - zFalse) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ZeroKnowledgeTheoremProving/AffineDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ZeroKnowledgeTheoremProving/AffineDuality.lean#L96

-- Thm stub generated from Applications/ZeroKnowledgeTheoremProving/AffineDuality.lean
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

theorem ZeroKnowledgeTheoremProving.AffineDuality.special_soundness(s : Statement (G := G) (H := H))
    (a : H) (zFalse zTrue : G)
    (hFalse : Accepts s ⟨a, false, zFalse⟩)
    (hTrue : Accepts s ⟨a, true, zTrue⟩) :
    IsWitness s (zTrue - zFalse) := by sorry
