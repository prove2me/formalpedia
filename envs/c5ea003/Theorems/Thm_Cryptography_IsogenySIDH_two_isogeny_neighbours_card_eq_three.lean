-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_two_isogeny_neighbours_card_eq_three
-- name    : Cryptography.IsogenySIDH.two_isogeny_neighbours_card_eq_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:28.983921+00:00
-- url     : https://prove2.me/theorems/7629ef2b-ea8f-48ce-9e8d-0fb97f7540db
-- title:
--   Exactness of the bound `3`.
-- statement:
--   **Exactness of the bound `3`.**  If the three neighbours are pairwise
--   distinct, the vertex `j(E_A)` of the 2-isogeny graph has exactly three
--   neighbours: the bound of `two_isogeny_neighbours_card_le_three` is attained, and
--   by `two_isogeny_neighbours_complete` nothing else occurs.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.two_isogeny_neighbours_card_eq_three[DecidableEq K] {A u₁ u₂ : K}
--       (hu₁ : u₁ ^ 2 + A ^ 2 * u₁ + A ^ 2 = 0) (hu₂ : u₂ ^ 2 + A ^ 2 * u₂ + A ^ 2 = 0)
--       (hd : A ^ 2 - 4 ≠ 0)
--       (h01 : jQuot A ≠ jOther A u₁) (h02 : jQuot A ≠ jOther A u₂)
--       (h12 : jOther A u₁ ≠ jOther A u₂) :
--       ∃ S : Finset K, S.card = 3 ∧ (∀ y, y ∈ S ↔ modPoly2 (jMont A) y = 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/MontgomeryModelFibres.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/MontgomeryModelFibres.lean#L123

-- Thm stub generated from Cryptography/IsogenySIDH/MontgomeryModelFibres.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_MontgomeryModelFibres
import Definitions.Def_Cryptography_IsogenySIDH_TwoIsogenyNeighbours
/-
# The six Montgomery models of one `j`-invariant, and the 6-to-3 fibration

`ModularTwoIsogeny` proved two counting *bounds*: a vertex of the 2-isogeny
graph has at most three neighbours, and a `j`-invariant has at most six
Montgomery models.  The previous cycle's Conjecture 2 asserted that both bounds
are attained and that the radical map `jQuot` fibres the six models onto the
three neighbours in pairs.  This file proves that, using the explicit second and
third Montgomery models constructed in `TwoIsogenyNeighbours`.

Given `A` with `A² ≠ 4` and the two roots `u₁ ≠ u₂` of `u² + A²u + A² = 0`, the
six Montgomery models of `E_A` are

  `± A`,  `± A₁`,  `± A₂`,   where `A₁² = tShift A u₁`, `A₂² = tShift A u₂`,

`± A₁` and `± A₂` being the models obtained by moving the two other two-torsion
points to the origin (these live over `K(√(A²-4), √(-A r - 2))`).

* `jMont_of_shift_root` — each `Aᵢ` is indeed a Montgomery model of the *same*
  curve, and is nondegenerate.
* `montgomery_models_complete` — **exactness of the bound `6`**: as soon as the
  six listed parameters are distinct, they are *all* the Montgomery models: any
  `B` with `j(E_B) = j(E_A)` and `B² ≠ 4` is one of them.
* `jQuot_of_shift_root`, `jQuot_image_of_models` — **the 6-to-3 fibration**: the
  radical map `jQuot` sends the six models onto exactly the three neighbours
  `jQuot A`, `jOther A u₁`, `jOther A u₂`, with fibres `{A, -A}`, `{A₁, -A₁}`,
  `{A₂, -A₂}` — the two members of a fibre differing by the sign of the radical,
  i.e. by the quadratic twist of the *model*.
* `two_isogeny_neighbours_card_eq_three` — **exactness of the bound `3`**: the
  vertex `j(E_A)` has exactly three neighbours in the 2-isogeny graph.
-/

set_option maxHeartbeats 1000000

open Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## The shifted models -/




/-! ## Exactness of the bound six -/




/-! ## The 6-to-3 fibration -/

theorem Cryptography.IsogenySIDH.two_isogeny_neighbours_card_eq_three[DecidableEq K] {A u₁ u₂ : K}
    (hu₁ : u₁ ^ 2 + A ^ 2 * u₁ + A ^ 2 = 0) (hu₂ : u₂ ^ 2 + A ^ 2 * u₂ + A ^ 2 = 0)
    (hd : A ^ 2 - 4 ≠ 0)
    (h01 : jQuot A ≠ jOther A u₁) (h02 : jQuot A ≠ jOther A u₂)
    (h12 : jOther A u₁ ≠ jOther A u₂) :
    ∃ S : Finset K, S.card = 3 ∧ (∀ y, y ∈ S ↔ modPoly2 (jMont A) y = 0) := by sorry
