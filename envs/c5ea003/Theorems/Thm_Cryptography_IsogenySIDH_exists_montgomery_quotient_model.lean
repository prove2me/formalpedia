-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_exists_montgomery_quotient_model
-- name    : Cryptography.IsogenySIDH.exists_montgomery_quotient_model
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:42:03.136651+00:00
-- url     : https://prove2.me/theorems/7aa8375e-6e4f-42eb-a1ff-c3c1932d3122
-- title:
--   The quotient curve always has a Montgomery model over the same field.
-- statement:
--   **The quotient curve always has a Montgomery model over the same field.**
--   If `-1` is a square in the finite field `F` of odd characteristic and `A² ≠ 4`,
--   then some `A' ∈ F` is a Montgomery parameter for the curve `2`-isogenous to
--   `E_A` via `⟨(0,0)⟩`; i.e. `jMont A' = jQuot A`.  No field extension is ever
--   needed for a radical walk over `𝔽_{p²}`.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.exists_montgomery_quotient_model(hF : ringChar F ≠ 2)
--       (hneg : IsSquare (-1 : F)) {A : F} (hd : A ^ 2 - 4 ≠ 0) :
--       ∃ A' : F, jMont A' = jQuot A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/SupersingularRadicalExistence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/SupersingularRadicalExistence.lean#L95

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

theorem Cryptography.IsogenySIDH.exists_montgomery_quotient_model(hF : ringChar F ≠ 2)
    (hneg : IsSquare (-1 : F)) {A : F} (hd : A ^ 2 - 4 ≠ 0) :
    ∃ A' : F, jMont A' = jQuot A := by sorry
