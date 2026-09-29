-- Prove2me | solution 1 for GradedTransitivity.trivial_family_denominator_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:55:57.37513+00:00
-- url     : https://prove2.me/submissions/0c217d4e-b7a3-4196-9851-6e829025120d

-- Sol generated from Shared/GradedTransitivity/Sharpness.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet
import Definitions.Def_Shared_GradedTransitivity_Newton
import Theorems.Thm_GradedTransitivity_sdiff_iter_choose
import Theorems.Thm_GradedTransitivity_sdiff_iter_const_mul
import Theorems.Thm_GradedTransitivity_sdiff_iter_eventuallyZero_iff
import Theorems.Thm_GradedTransitivity_torbits_of_trivial_action

/-!
# Sharpness of the exponent in the `G`-set setting

The main theorem says that *eventual `r`-transitivity* gives denominator
`(1-q)`, hence a fortiori a denominator dividing `(1-q)^{r+1}`.  Is the
exponent `r+1` in the general statement wasteful?  No: as soon as
transitivity is dropped, the exponent `r+1` is attained *and needed*.

We exhibit this with the graded `G`-set `Y_n = Fin n` acted on by the trivial
group `G_n = ⊥ ≤ Perm (Fin n)`.  Here every injective `r`-tuple is its own
orbit, so

`t_r(Y_n) = n(n-1)⋯(n-r+1) = r! · C(n,r)`,

whose generating function is `r!·q^r/(1-q)^{r+1}` — a genuine pole of order
`r+1` at `q = 1`.

## Main results

* `torbits_of_trivial_action` : trivial actions count injective tuples.
* `torbits_bot` : `t_r = n.descFactorial r` for the trivial-group family.
* `trivial_family_generating_function` : the exact Hilbert series.
* `trivial_family_denominator_sharp` : `(1-q)^r` does *not* suffice, so the
  exponent `r+1` of the main theorem is optimal in the absence of
  transitivity.
-/

open GradedTransitivity

open Polynomial

/-! ### Trivial actions -/


/-! ### The trivial-group graded set -/

/-- For the trivial subgroup of `Perm (Fin n)` acting on `Fin n`, the number of
orbits of injective `r`-tuples is the falling factorial. -/
theorem torbits_bot (r n : ℕ) :
    torbits (⊥ : Subgroup (Equiv.Perm (Fin n))) (Fin n) r = n.descFactorial r := by
  rw [torbits_of_trivial_action (fun g y => by
    have : (g : Equiv.Perm (Fin n)) = 1 := by
      simpa using (Subgroup.mem_bot.1 g.2)
    show (g : Equiv.Perm (Fin n)) • y = y
    rw [this, one_smul]) r]
  simp [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]


/-- The Hilbert series of the trivial-group family is `r! · C(n,r)`. -/
theorem hilbertSeq_bot (r : ℕ) :
    hilbertSeq (fun n => (⊥ : Subgroup (Equiv.Perm (Fin n)))) (fun n => Fin n) r
      = fun n => (r.factorial : ℚ) * chooseSeq r n := by
  funext n
  simp only [hilbertSeq, torbits_bot, chooseSeq]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring





open GradedTransitivity in
theorem solution(r : ℕ) :
    ¬ ∃ P : ℚ[X], (1 - PowerSeries.X) ^ r *
        gen (hilbertSeq (fun n => (⊥ : Subgroup (Equiv.Perm (Fin n)))) (fun n => Fin n) r)
      = (P : PowerSeries ℚ) := by
  intro h
  rw [hilbertSeq_bot r] at h
  have hz : EventuallyZero (sdiff^[r] (fun n => (r.factorial : ℚ) * chooseSeq r n)) :=
    (sdiff_iter_eventuallyZero_iff r _).1 h
  rw [sdiff_iter_const_mul (r.factorial : ℚ) (chooseSeq r) r] at hz
  obtain ⟨N, hN⟩ := hz
  have hval := hN N le_rfl
  rw [show chooseSeq r = chooseSeq (0 + r) by rw [Nat.zero_add], sdiff_iter_choose r 0] at hval
  simp only [chooseSeq, Nat.choose_zero_right, Nat.cast_one, mul_one] at hval
  have : (r.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
  exact this hval
