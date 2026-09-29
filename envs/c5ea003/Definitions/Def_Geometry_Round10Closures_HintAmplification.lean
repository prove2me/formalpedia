-- Prove2me | Definitions.Def_Geometry_Round10Closures_HintAmplification
-- name    : Geometry_Round10Closures_HintAmplification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:51.056456+00:00
-- url     : https://prove2.me/theorems/3887d870-5f76-448e-84ef-108a7458f321
-- title:
--   Aether Catalog definitions — Geometry_Round10Closures_HintAmplification
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Round10Closures.HintAmplification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Round10Closures/HintAmplification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_Round10Closures_JointClosure
/-
Round-10 Closures — Part V: pricing the hint (HINT-AMP scope restatement).

The round-10 batch flagged hint amplification (Coppersmith, partial key exposure) as the
one resource the barrier framework never priced, because it is not extraction from `N`
alone: it consumes an *external* hint.  This file makes the scope restatement precise in
the simplest possible model of a hint — the trace `p + q` of the factorisation — and proves
that this single hint is amplified to the full factorisation by an explicit, closed-form,
constant-time extractor:

    factorFromTrace N s = (s - sqrt (s² - 4N)) / 2 .

Contrast with `JointClosure.no_profile_extractor`, where no extractor whatsoever exists for
the hint-free free-witness channel: the two theorems together delimit the framework's
scope, "extraction from `N` alone" versus "amplification of hints".
-/

namespace Round10

/-- The closed-form extractor: recover the smaller factor of `N` from the hint `s = p + q`. -/
def factorFromTrace (N s : ℕ) : ℕ := (s - Nat.sqrt (s * s - 4 * N)) / 2




end Round10


