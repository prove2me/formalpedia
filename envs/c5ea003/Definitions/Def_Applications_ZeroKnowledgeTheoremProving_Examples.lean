-- Prove2me | Definitions.Def_Applications_ZeroKnowledgeTheoremProving_Examples
-- name    : Applications_ZeroKnowledgeTheoremProving_Examples
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T01:00:42.794609+00:00
-- url     : https://prove2.me/theorems/196a4870-bff3-438c-bc18-dba76ed10dac
-- title:
--   Aether Catalog definitions — Applications_ZeroKnowledgeTheoremProving_Examples
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ZeroKnowledgeTheoremProving.Examples`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ZeroKnowledgeTheoremProving/Examples.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries

/-!
# A Concrete Instance: the Affine Σ-Protocol over `ZMod 12`

The theorems of `AffineDuality`, `ProvabilityAmplification` and
`EntropyAndBoundaries` are stated for an arbitrary public homomorphism of
abelian groups. This file certifies that they are *not vacuous* by exhibiting a
fully computable instance and checking every hypothesis by decision procedure.

Take `G = H = ZMod 12` and the public homomorphism `x ↦ 4 * x`.

* `trueStatement` has target `8`, which lies in the image `{0, 4, 8}`.
  It has exactly four witnesses `{2, 5, 8, 11}`, matching the four kernel
  elements `{0, 3, 6, 9}` as predicted by `card_witnesses_eq_card_ker`.
* `falseStatement` has target `1`, which is not in the image, so it has no
  witness at all; `soundness_error_le` then bounds a committed prover's success
  over `n` rounds by `(1/2) ^ n` — for `n = 10` that is `1/1024`
  (`falseStatement_soundness_10`).
* Extraction really works on numbers (`example_extraction`), and the two
  distinct witnesses `2` and `5` generate literally the same transcript
  multiset (`example_witness_indistinguishable`), so the verifier cannot tell
  them apart even in this tiny group.
-/

namespace ZeroKnowledgeTheoremProving.AffineDuality.Examples

open ZeroKnowledgeTheoremProving.AffineDuality

/-- Multiplication by `4` on `ZMod 12`, as an additive homomorphism. -/
def mulFour : ZMod 12 →+ ZMod 12 :=
  AddMonoidHom.mk' (fun x => 4 * x) (by intro a b; ring)

/-- A true public statement: `4 * w = 8` is solvable. -/
def trueStatement : Statement (G := ZMod 12) (H := ZMod 12) :=
  ⟨mulFour, 8⟩

/-- A false public statement: `4 * w = 1` has no solution in `ZMod 12`. -/
def falseStatement : Statement (G := ZMod 12) (H := ZMod 12) :=
  ⟨mulFour, 1⟩











end ZeroKnowledgeTheoremProving.AffineDuality.Examples


