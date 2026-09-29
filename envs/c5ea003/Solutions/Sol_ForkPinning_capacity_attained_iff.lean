-- Prove2me | solution 1 for ForkPinning.capacity_attained_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:40:07.733923+00:00
-- url     : https://prove2.me/submissions/65032937-f118-46f8-86bd-e2e5caa2c6fa

-- Sol generated from Probability/ForkPinningCapacity.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
import Theorems.Thm_ForkPinning_entropy_bool_eq_log_two_iff
import Theorems.Thm_ForkPinning_entropy_le_log_card
import Theorems.Thm_ForkPinning_mutualInfo_le_entropy
import Theorems.Thm_ForkPinning_pinned_iff_determines
/-
# Capacity of a binary fork: one bit, attained exactly at the balanced coset forks

`ForkPinningCore` proves the two capacity bounds `I(X;Y) ≤ H Y` and `I(X;Y) ≤ log |κ|`.  For a
*binary* fork these combine into the hard ceiling `I ≤ log 2`: no congruence observable, however
large its conductor, can extract more than one bit from a two-valued splitting statistic.  This
file closes conjecture **C2** of `FUTURE_DIRECTIONS.md` by determining exactly when the ceiling
is attained.

Main results:

* `ForkPinning.entropy_bool_eq_log_two_iff` : `H Y = log 2` iff the fork is balanced (the strict
  maximum-entropy statement for two-valued statistics).
* `ForkPinning.mutualInfo_bool_le_log_two` : the one-bit ceiling.
* `ForkPinning.capacity_attained_iff` : `I(X;Y) = log 2` **iff** `X` determines `Y` *and* `Y` is
  balanced — capacity is attained exactly at the balanced forks that the observable pins.
* `ForkPinning.prb_hom_uniform` : a surjective character is uniformly distributed on a uniform
  group (the counting input).
* `ForkPinning.prb_signBool_true` : the sign of a uniformly random permutation of `Fin n`,
  `n ≥ 2`, is balanced.
* `ForkPinning.sign_attains_capacity` and `ForkPinning.sign_capacity_attained_iff` : for `Sₙ`
  the supremum `log 2` is attained, and *only* by the two forks `sign` and `¬sign` — the exact
  formal counterpart of the measurement "the only congruence structure in the whole `S₄`
  splitting is the sign".
-/


open ForkPinning

open Finset Real

/-! ## The strict maximum-entropy statement for binary forks -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]







/-! ## The one-bit ceiling and its attainment -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]




/-! ## Surjective characters are uniform -/


variable {G : Type*} [Group G] [Fintype G] [Nonempty G]
variable {A : Type*} [Group A] [Fintype A] [DecidableEq A]




/-! ## The sign character attains the capacity, and nothing else does -/


variable {n : ℕ}







open ForkPinning in
theorem solution(X : Ω → κ) (Y : Ω → Bool) :
    mutualInfo X Y = Real.log 2 ↔ Determines X Y ∧ prb Y true = 1 / 2 := by
  constructor
  · intro hI
    have hHY : H Y ≤ Real.log 2 := by
      have hcard : (Fintype.card Bool : ℝ) = 2 := by norm_num
      have := entropy_le_log_card (Ω := Ω) Y
      rwa [hcard] at this
    have hle : mutualInfo X Y ≤ H Y := mutualInfo_le_entropy X Y
    have hHeq : H Y = Real.log 2 := le_antisymm hHY (by rw [← hI]; exact hle)
    refine ⟨(pinned_iff_determines X Y).mp (by rw [hI, hHeq]), ?_⟩
    exact (entropy_bool_eq_log_two_iff Y).mp hHeq
  · rintro ⟨hdet, hbal⟩
    rw [(pinned_iff_determines X Y).mpr hdet]
    exact (entropy_bool_eq_log_two_iff Y).mpr hbal
