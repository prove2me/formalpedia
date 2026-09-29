-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_not_injective_at_eight_of_not_exactlyOne
-- name    : Cryptography.TernaryReversible.not_injective_at_eight_of_not_exactlyOne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:46:20.439677+00:00
-- url     : https://prove2.me/theorems/3e0c5516-64ca-42de-b0cc-8c405c9b8b71
-- title:
--   Every affine kernel obstruction, whatever its native length `1`, `2`, `4` or `8`, is
-- statement:
--   Every affine kernel obstruction, whatever its native length `1`, `2`, `4` or `8`, is
--   already visible on the cycle of length `8`.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.not_injective_at_eight_of_not_exactlyOne{α β γ δ : Alph}
--       (h : ¬ ExactlyOneNonzero α β γ) :
--       ¬ Function.Injective (globalMap (n := 8) (addRule α β γ δ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/AffineTest.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/AffineTest.lean#L33

-- Thm stub generated from Cryptography/TernaryReversible/AffineTest.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Additive
import Definitions.Def_Cryptography_TernaryReversible_Core

/-!
# A single cycle length decides reversibility of affine ternary rules

`Additive.lean` shows that an affine rule `addRule α β γ δ` is bijective on every finite
cycle iff exactly one of `α, β, γ` is nonzero, the obstruction in the remaining cases being
a kernel vector living on a cycle of length `1`, `2`, `4` or `8` (the orders of the roots
of unity available in `𝔽₉ˣ`).

Combining this with the divisor monotonicity of `Periodicity.lean` — injectivity at length
`n` implies injectivity at every divisor of `n` — all four bad lengths can be *pulled up
into the single length* `8`, because `1, 2, 4, 8` all divide `8`.  The infinite test
"bijective on every cycle" therefore collapses, inside the affine class, to **one finite
test on the `8`-cycle**, i.e. to injectivity of a single map on `3⁸ = 6561` states.

## Main results

* `not_injective_at_eight_of_not_exactlyOne` — every affine obstruction is visible at
  length `8`;
* `addRule_cycleBijective_iff_injective_at_eight` — the one-length criterion;
* `addRule_bad_lengths_multiples_of_eight` — a non-reversible affine rule fails on *every*
  multiple of `8`, hence on infinitely many cycle lengths.
-/

open Cryptography
open TernaryReversible

theorem Cryptography.TernaryReversible.not_injective_at_eight_of_not_exactlyOne{α β γ δ : Alph}
    (h : ¬ ExactlyOneNonzero α β γ) :
    ¬ Function.Injective (globalMap (n := 8) (addRule α β γ δ)) := by sorry
