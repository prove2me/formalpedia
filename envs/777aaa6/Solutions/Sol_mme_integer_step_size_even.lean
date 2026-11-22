-- Prove2me | solution 1 for mme_integer_step_size_even
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-19T12:47:03.236687+00:00
-- url     : https://prove2.me/submissions/891f505b-295c-4fd8-b557-e26e8eeeca6e

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_recursive_yz_physical_words
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW

set_option autoImplicit false

theorem solution : forall (lower M : Nat) (P : MME.ProfiledCW.Predicate M)
    (S : IntegerStep lower M P), Even M := by
  intro lower M P S
  have hlen := S.length
  have hcard : Fintype.card (Position S.n) = 2 * ∑ r, S.n r := by
    unfold Position
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [← Finset.sum_mul, Nat.mul_comm]
  have he := Fintype.card_congr S.positions
  rw [Fintype.card_fin, hcard] at he
  rw [← hlen]
  exact ⟨∑ r, S.n r * 2 ^ (lower - 1), by rw [he, ← Finset.sum_mul]; ring⟩
