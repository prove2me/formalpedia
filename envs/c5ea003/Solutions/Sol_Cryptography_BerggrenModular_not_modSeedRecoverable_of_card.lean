-- Prove2me | solution 1 for Cryptography.BerggrenModular.not_modSeedRecoverable_of_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:27:51.908901+00:00
-- url     : https://prove2.me/submissions/e4aa93ae-48af-45ba-8236-ac87adc97d55

-- Sol generated from Cryptography/BerggrenModular/Hardness.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Hardness
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Theorems.Thm_Cryptography_BerggrenModular_card_words
import Theorems.Thm_Cryptography_BerggrenModular_not_modSeedRecoverable_of_collision

/-!
# Seed recovery: easy over `ℤ`, information-theoretically hard over `ℤ/m`

Fix the Berggren root `(3,4,5)` and a *control word* `u ∈ {B₁,B₂,B₃}^k`.  The
*seed-recovery problem* asks: from the single observed state `applyWord u root`,
reconstruct `u`.

* Over `ℤ` this is **easy**: `recoverFrom` solves it with `k` comparisons and `k`
  linear maps (`intSeedRecoverable`).  This is a corollary of the exactness of the
  classifier `whichMove` together with the freeness of the Berggren monoid.

* Over `ℤ/m` the same problem becomes **impossible** once `k` is large compared to
  the modulus, and quantitatively ambiguous long before that:

  - `mod_ambiguity_lower_bound` : for every `n` with `m³·n < 3^k` there is an
    observed modular state with more than `n` consistent control words.  Taking
    `n = ⌈3^k/m³⌉ − 1` this is the promised `Ω(3^k / poly(m))` bound: the
    modulus is polynomial-size, the ambiguity is exponential.
  - `not_modSeedRecoverable_of_card` : if `m³ < 3^k` no recovery function exists.
  - `not_modSeedRecoverable_of_dl` : recovery for *all* words of length `≤ k`
    would in particular solve the discrete-logarithm problem for the matrix `B₂`
    modulo `m`; and that problem is already unsolvable for `k ≥ m³` because the
    `B₂`-orbit has collided by then.  This is the precise sense of
    "hard unless the `B₂` discrete logarithm mod `m` is easy".

## Main results

* `intSeedRecoverable`
* `mod_ambiguity_lower_bound`
* `not_modSeedRecoverable_of_card`
* `dlEasy_of_modSeedRecoverable`
* `not_dlEasy_of_large`
* `berggren_modulus_separation` — the combined statement.
-/

open Cryptography
open BerggrenModular

/-! ## Integer seed recovery is easy -/





/-! ## The modular observation -/




/-! ## Counting: `3^k` control words versus `m³` states -/


theorem card_TriM (m : ℕ) [NeZero m] : Fintype.card (TriM m) = m ^ 3 := by
  simp only [TriM, Fintype.card_prod, ZMod.card]
  ring



/-- Two distinct control words of the same length `k` collide modulo `m`
as soon as `m³ < 3^k`. -/
theorem exists_mod_collision (m k : ℕ) [NeZero m] (h : m ^ 3 < 3 ^ k) :
    ∃ u w : List Move, u.length = k ∧ w.length = k ∧ u ≠ w ∧ stateMod m u = stateMod m w := by
  have hcard : Fintype.card (TriM m) < Fintype.card (Fin k → Move) := by
    rw [card_TriM, card_words]; exact h
  obtain ⟨u, w, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (stateModF m k) hcard
  refine ⟨List.ofFn u, List.ofFn w, List.length_ofFn, List.length_ofFn, ?_, heq⟩
  intro hEq
  exact hne (List.ofFn_injective hEq)


/-! ## The `B₂` discrete logarithm -/







/-! ## The separation -/



open Cryptography.BerggrenModular in
theorem solution(m k : ℕ) [NeZero m] (h : m ^ 3 < 3 ^ k) :
    ¬ ModSeedRecoverable m k := by
  obtain ⟨u, w, hu, hw, hne, hcol⟩ := exists_mod_collision m k h
  exact not_modSeedRecoverable_of_collision (le_of_eq hu) (le_of_eq hw) hne hcol
