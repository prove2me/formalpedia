-- Prove2me | solution 1 for Cryptography.IsogenySIDH.two_isogeny_neighbours_card_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:58:10.810747+00:00
-- url     : https://prove2.me/submissions/43e7374d-9fe8-499c-9a77-e8720aa79232

-- Sol generated from Cryptography/IsogenySIDH/MontgomeryModelFibres.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_MontgomeryModelFibres
import Definitions.Def_Cryptography_IsogenySIDH_TwoIsogenyNeighbours
import Theorems.Thm_Cryptography_IsogenySIDH_modPoly2_jMont_jOther
import Theorems.Thm_Cryptography_IsogenySIDH_modPoly2_jMont_jQuot
import Theorems.Thm_Cryptography_IsogenySIDH_two_isogeny_neighbours_complete
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




open Cryptography.IsogenySIDH in
theorem solution[DecidableEq K] {A u₁ u₂ : K}
    (hu₁ : u₁ ^ 2 + A ^ 2 * u₁ + A ^ 2 = 0) (hu₂ : u₂ ^ 2 + A ^ 2 * u₂ + A ^ 2 = 0)
    (hd : A ^ 2 - 4 ≠ 0)
    (h01 : jQuot A ≠ jOther A u₁) (h02 : jQuot A ≠ jOther A u₂)
    (h12 : jOther A u₁ ≠ jOther A u₂) :
    ∃ S : Finset K, S.card = 3 ∧ (∀ y, y ∈ S ↔ modPoly2 (jMont A) y = 0) := by
  refine ⟨{jQuot A, jOther A u₁, jOther A u₂}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
  · intro y
    constructor
    · intro hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact modPoly2_jMont_jQuot hd
      · exact modPoly2_jMont_jOther hu₁ hd
      · exact modPoly2_jMont_jOther hu₂ hd
    · intro hy
      have := two_isogeny_neighbours_complete hu₁ hu₂ hd h01 h02 h12 hy
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
