-- Prove2me | solution 1 for Cryptography.IsogenySIDH.montModels_are_models
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:47:44.679701+00:00
-- url     : https://prove2.me/submissions/41011f95-9ac1-4938-8206-750846444bc8

-- Sol generated from Cryptography/IsogenySIDH/MontgomeryModelFibres.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_MontgomeryModelFibres
import Definitions.Def_Cryptography_IsogenySIDH_TwoIsogenyNeighbours
import Theorems.Thm_Cryptography_IsogenySIDH_jMont_eq_jMontSq
import Theorems.Thm_Cryptography_IsogenySIDH_jMont_neg
import Theorems.Thm_Cryptography_IsogenySIDH_tShift_sub_four_ne_zero
import Theorems.Thm_Cryptography_IsogenySIDH_two_torsion_shift_j_invariant
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

/-- A square root of `tShift A u` is a Montgomery parameter of the *same* curve
`E_A`. -/
theorem jMont_of_shift_root {A u B : K} (hu : u ^ 2 + A ^ 2 * u + A ^ 2 = 0)
    (hd : A ^ 2 - 4 ≠ 0) (hB : B ^ 2 = tShift A u) : jMont B = jMont A := by
  rw [jMont_eq_jMontSq, hB]
  exact two_torsion_shift_j_invariant hu hd

/-- The shifted models are nondegenerate. -/
theorem shift_root_ne_two {A u B : K} (hu : u ^ 2 + A ^ 2 * u + A ^ 2 = 0)
    (hd : A ^ 2 - 4 ≠ 0) (hB : B ^ 2 = tShift A u) : B ^ 2 - 4 ≠ 0 := by
  rw [hB]
  exact tShift_sub_four_ne_zero hu hd


/-! ## Exactness of the bound six -/




/-! ## The 6-to-3 fibration -/




open Cryptography.IsogenySIDH in
theorem solution[DecidableEq K] {A A₁ A₂ u₁ u₂ : K}
    (hu₁ : u₁ ^ 2 + A ^ 2 * u₁ + A ^ 2 = 0) (hu₂ : u₂ ^ 2 + A ^ 2 * u₂ + A ^ 2 = 0)
    (hd : A ^ 2 - 4 ≠ 0) (h1 : A₁ ^ 2 = tShift A u₁) (h2 : A₂ ^ 2 = tShift A u₂) :
    ∀ B ∈ montModels A A₁ A₂, B ^ 2 - 4 ≠ 0 ∧ jMont B = jMont A := by
  intro B hB
  simp only [montModels, Finset.mem_insert, Finset.mem_singleton] at hB
  have hneg : ∀ C : K, (-C) ^ 2 - 4 = C ^ 2 - 4 := by intro C; ring
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hd, rfl⟩
  · exact ⟨by rw [hneg]; exact hd, jMont_neg A⟩
  · exact ⟨shift_root_ne_two hu₁ hd h1, jMont_of_shift_root hu₁ hd h1⟩
  · exact ⟨by rw [hneg]; exact shift_root_ne_two hu₁ hd h1,
      by rw [jMont_neg]; exact jMont_of_shift_root hu₁ hd h1⟩
  · exact ⟨shift_root_ne_two hu₂ hd h2, jMont_of_shift_root hu₂ hd h2⟩
  · exact ⟨by rw [hneg]; exact shift_root_ne_two hu₂ hd h2,
      by rw [jMont_neg]; exact jMont_of_shift_root hu₂ hd h2⟩
