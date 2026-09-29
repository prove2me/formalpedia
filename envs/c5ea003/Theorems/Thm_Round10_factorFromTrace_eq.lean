-- Prove2me | Theorems.Thm_Round10_factorFromTrace_eq
-- name    : Round10.factorFromTrace_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:05.255805+00:00
-- url     : https://prove2.me/theorems/c1ed2161-d6e4-404d-a5b9-8dcf99a8439e
-- title:
--   Hint amplification.
-- statement:
--   **Hint amplification.**  The additive hint `p + q` amplifies to the full factorisation
--   of `N = p * q` in closed form.
--
--   ```lean
--   theorem Round10.factorFromTrace_eq{p q : ℕ} (hpq : p ≤ q) : factorFromTrace (p * q) (p + q) = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/HintAmplification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/HintAmplification.lean#L23

-- Thm stub generated from Geometry/Round10Closures/HintAmplification.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_HintAmplification
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

open Round10

theorem Round10.factorFromTrace_eq{p q : ℕ} (hpq : p ≤ q) : factorFromTrace (p * q) (p + q) = p := by sorry
