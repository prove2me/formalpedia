-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_isSquare_neg_one_of_card_sq
-- name    : Cryptography.IsogenySIDH.isSquare_neg_one_of_card_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:42:11.524656+00:00
-- url     : https://prove2.me/theorems/a5e7543b-5f01-4b22-92c2-db17cf8c73e2
-- title:
--   In a finite field whose cardinality is a perfect square — in particular in
-- statement:
--   In a finite field whose cardinality is a perfect square — in particular in
--   `𝔽_{p²}` for odd `p` — the element `-1` is a square.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.isSquare_neg_one_of_card_sq(hF : ringChar F ≠ 2) {q : ℕ}
--       (hcard : Fintype.card F = q ^ 2) : IsSquare (-1 : F) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/SupersingularRadicalExistence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/SupersingularRadicalExistence.lean#L71

-- Thm stub generated from Cryptography/IsogenySIDH/SupersingularRadicalExistence.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_SupersingularRadicalExistence
/-
# Radicals always exist over quadratic finite fields

Radical isogeny algorithms are run on supersingular curves over `𝔽_{p²}`.  A
radical 2-isogeny step from the Montgomery parameter `A` needs a square root of
`A + 2`; if that root is missing one has to change the Montgomery model, using
instead `√(2-A)` or `√(A²-4)` (see `ModularTwoIsogeny`, where all three models
were shown to hit the same point of the `j`-line).

The main theorem of this file, `exists_radical_of_isSquare_neg_one`, is that at
least one of these three radicals is *always* available, as soon as `-1` is a
square in the base field.  The proof is a quadratic-character computation
resting on the identity

`(A+2)·(2-A) = -(A²-4)`,

so the three radicands multiply to minus a square: their quadratic characters
cannot all be `-1`.

`isSquare_neg_one_of_card_sq` specialises this to a field of square
cardinality — exactly the quadratic finite fields `𝔽_{p²}` of supersingular
isogeny cryptography — where `-1` is automatically a square.  Combined with the
model-independence theorem of `ModularTwoIsogeny` this yields
`exists_montgomery_quotient_model`: over `𝔽_{p²}` the 2-isogenous curve always
has a Montgomery model defined over the same field, so a radical walk never
needs a field extension.

The final section records small, fully checked supersingular instances of the
radical step, verified by `decide`.
-/

open Cryptography.IsogenySIDH

open Finset

/-! ## Existence of one of the three radicals -/


variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]



omit [DecidableEq F] in

theorem Cryptography.IsogenySIDH.isSquare_neg_one_of_card_sq(hF : ringChar F ≠ 2) {q : ℕ}
    (hcard : Fintype.card F = q ^ 2) : IsSquare (-1 : F) := by sorry
