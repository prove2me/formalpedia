-- Prove2me | Definitions.Def_Cryptography_TernaryReversible_Refutation
-- name    : Cryptography_TernaryReversible_Refutation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:59.599126+00:00
-- url     : https://prove2.me/theorems/220b65f4-23fd-4e3a-be34-7ce3135daa69
-- title:
--   Aether Catalog definitions — Cryptography_TernaryReversible_Refutation
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.TernaryReversible.Refutation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/TernaryReversible/Refutation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core

/-!
# Refutation of the single-coordinate classification claim

The claim under test: *every* local rule `Fin 3 → Fin 3 → Fin 3 → Fin 3` whose global
maps are bijective on all nonempty finite cycles is a single coordinate of the window
followed by a permutation of `Fin 3` (there are exactly `3 * 6 = 18` such rules).

This file **refutes** the claim by an explicit algebraic construction.  Write the
alphabet as the field `Fin 3 ≅ 𝔽₃`, whose units are `{1, 2} = {±1}`.  For a unit `u`
let `sgn u x = 1` if `x = 0` and `= u` otherwise; this is an *even* function of `x`
(`sgn u (-x) = sgn u x`) with values in the units.  The **sign-twisted rules**

`signRule u v a b c = sgn u a * b * sgn v c`

multiply the middle cell by a unit read off from the two neighbours.  Because the
twist only depends on *whether* a neighbour vanishes — information that survives
multiplication by a unit — the twist can be recomputed from the output, so each such
rule decodes itself: it is an **involution on every finite cycle**, in particular
bijective there.  For `u = v = 2` the rule genuinely depends on all three coordinates,
so it is not of the predicted form.

## Main results

* `signRule_selfDecoder`, `signRule_involution`, `signRule_cycleBijective`;
* `gStar_cycleBijective`, `gStar_not_singleCoordinatePerm`;
* `classification_claim_false` — the falsifiable claim is **false**;
* `eighteen_counterexamples` — there are at least `18` cycle-bijective rules outside
  the predicted list, i.e. as many counterexamples as the claim allows rules in total.
-/

namespace Cryptography
namespace TernaryReversible

/-! ## Units of `Fin 3` and the sign twist -/

/-- The units of `Fin 3`, i.e. `±1`. -/
def IsSign (u : Alph) : Prop := u = 1 ∨ u = 2

instance : DecidablePred IsSign := fun u => by unfold IsSign; infer_instance

/-- `sgn u x` is `1` when `x = 0` and `u` otherwise: an even, unit-valued function. -/
def sgn (u x : Alph) : Alph := if x = 0 then 1 else u




/-! ## The sign-twisted rules and their self-decoding -/

/-- The sign-twisted rule `a b c ↦ sgn u a * b * sgn v c`. -/
def signRule (u v : Alph) : LocalRule := fun a b c => sgn u a * b * sgn v c




/-! ## The explicit counterexample -/

/-- The counterexample rule `g⋆ a b c = sgn 2 a * b * sgn 2 c`, i.e. the middle cell
negated once for each nonzero neighbour. -/
def gStar : LocalRule := signRule 2 2









/-! ## Eighteen counterexamples: the claim misses at least as many rules as it predicts -/

/-- Sign-twisted rules post-composed with the affine permutation `x ↦ c * x + d`. -/
def famRule (u v c d : Alph) : LocalRule := fun a b x => c * (signRule u v a b x) + d




/-- The eighteen parameter tuples `(u, v, c, d)` with `u, v, c` units and `(u,v) ≠ (1,1)`. -/
def famParams : Finset (Alph × Alph × Alph × Alph) :=
  Finset.univ.filter (fun p => (p.1 = 2 ∨ p.2.1 = 2) ∧ IsSign p.1 ∧ IsSign p.2.1 ∧
    IsSign p.2.2.1)

/-- The corresponding eighteen local rules. -/
def famSet : Finset LocalRule := famParams.image (fun p => famRule p.1 p.2.1 p.2.2.1 p.2.2.2)




end TernaryReversible
end Cryptography


