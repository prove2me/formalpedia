-- Prove2me | solution 1 for mme_numerical_package_step_boundary
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-09-22T21:16:41.395225+00:00
-- url     : https://prove2.me/submissions/dfab3af2-8a71-4bf9-bdf0-e6789b352d52

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_yz_physical_words
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
set_option autoImplicit false

theorem solution :
    ¬ (exists (lower : Nat) (P : Predicate 3)
      (S : IntegerStep lower 3 P) (B : BoundaryEnd lower 3 S.output) (copies : Nat),
      0 < copies /\
        (((copies * 8 ^ S.repairExponent : Nat)) : Real) <= S.entropyLower /\
        15625 <= B.a * B.b * B.c) := by
  rintro ⟨lower, P, S, B, copies, hcopies, hentropy, hdim⟩
  have hlen := S.length
  have hcard : Fintype.card (Position S.n) = 2 * ∑ r, S.n r := by
    unfold Position
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [← Finset.sum_mul, Nat.mul_comm]
  have he := Fintype.card_congr S.positions
  rw [Fintype.card_fin, hcard] at he
  have heven : Even 3 := by
    rw [← hlen]
    exact ⟨∑ r, S.n r * 2 ^ (lower - 1), by
      rw [he, ← Finset.sum_mul]
      ring⟩
  rcases heven with ⟨k, hk⟩
  omega
