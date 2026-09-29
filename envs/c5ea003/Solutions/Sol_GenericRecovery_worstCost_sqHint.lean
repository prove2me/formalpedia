-- Prove2me | solution 1 for GenericRecovery.worstCost_sqHint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:43:23.201131+00:00
-- url     : https://prove2.me/submissions/1cdb68d2-635a-4bbf-a23b-6caa4b2082eb

-- Sol generated from Combinatorics/GenericRecoveryHintSharpness.lean
import Mathlib
import Definitions.Def_Combinatorics_DialThresholdNoAmplification
import Definitions.Def_Combinatorics_GenericRecoveryHintSharpness
import Definitions.Def_Combinatorics_GenericRecoveryHintTaxonomy
import Theorems.Thm_GenericRecovery_card_natSqFiber
import Theorems.Thm_GenericRecovery_cost_le_worstCost
/-
# GENERIC-RECOVERY, cycle II: the taxonomy is *tight*

Sequel to `Combinatorics.GenericRecoveryHintTaxonomy`.  Cycle I proved the
negative half of the hint taxonomy: a `t`-bit hint never cuts a candidate set by
more than `2^t`, parity-constrained value hints lose a bit, post-processing and
joining never help, and public hints are worthless.  A negative theory is only
as strong as its sharpness, and only as interesting as the *exact* deficit it
assigns to the borderline families.  This file supplies three sharpenings and
one bridge.

* **§1 Sharpness.**  `GenericRecovery.card_fiber_blockHint` and
  `GenericRecovery.image_blockHint`: on a candidate set of size `q·2^t` the
  block hint `p ↦ p / q` realises all `2^t` values with *every* fibre of size
  exactly `q = |S| / 2^t`.  Together with the master bound of cycle I, the
  reduction factor of a `t`-bit hint is exactly `2^t` — never more (cycle I),
  and attained (here).  Hints are worth their bits at face value.
* **§2 Average case, not just worst case.**
  `GenericRecovery.sq_sum_cost_ge`: by Cauchy–Schwarz, the *expected* number of
  candidates the adversary must scan (over the induced distribution of hint
  readings) is at least `|S| / 2^t`.  The experiment measured medians equal to
  the class size; this is the theorem behind that observation, and it rules out
  a hint whose typical class is small while a few classes soak up the mass.
* **§3 The trace/square hint is worth `t - 3` bits, exactly.**
  `GenericRecovery.card_natSqFiber` (every fibre of `p ↦ p² mod 2^t` on the odd
  residues has exactly 4 elements) and
  `GenericRecovery.card_image_sqHint` (the hint therefore realises exactly
  `2^{t-3}` values).  A `t`-bit trace hint carries `t-3` usable bits: one bit to
  parity (§3 of cycle I), two bits to the square-root ambiguity.  This is the
  measured `log₂ C_t ≈ 3` deficit, now a theorem.
* **§4 Bridge to DIAL-THRESHOLD.**  `GenericRecovery.worstCost_dialVec_ge`:
  a residue-dial system is a hint of `log₂ (M*/gcd(M*,m))` bits and therefore
  obeys the master bound.  The two negative programmes are one programme.
-/

open GenericRecovery

open Finset

/-! ## 1.  Sharpness: the block hint attains the master bound exactly -/






/-! ## 2.  The average class is large too (Cauchy–Schwarz) -/

variable {α β : Type*} [DecidableEq β]



/-! ## 3.  The trace hint is worth exactly `t - 3` bits -/

/-- A candidate matching an odd square mod `2^t` is itself odd. -/
theorem odd_of_sq_congr {t x u : ℕ} (ht : 1 ≤ t) (hu : u % 2 = 1)
    (h : x ^ 2 % 2 ^ t = u ^ 2 % 2 ^ t) : x % 2 = 1 := by
  have hdvd : (2:ℕ) ∣ 2 ^ t := dvd_pow_self 2 (by omega)
  have h2 : x ^ 2 % 2 = u ^ 2 % 2 := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, ← Nat.mod_mod_of_dvd (u ^ 2) hdvd, h]
  rw [Nat.pow_mod, Nat.pow_mod u] at h2
  rw [hu] at h2
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  · rw [hx] at h2; simp at h2
  · exact hx




/-- On the odd residues the square hint still has four-element fibres: all four
square roots are odd. -/
theorem cost_sqHint (n u : ℕ) (hu : u ∈ oddResidues n) :
    cost (oddResidues n) (fun x => x ^ 2 % 2 ^ (n + 3)) (u ^ 2 % 2 ^ (n + 3)) = 4 := by
  have hu' : u % 2 = 1 := (Finset.mem_filter.mp hu).2
  rw [cost, ← card_natSqFiber n u hu']
  congr 1
  ext x
  simp only [oddResidues, Finset.mem_filter, mem_range]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, odd_of_sq_congr (by omega) hu' h2⟩, h2⟩



/-! ## 4.  Bridge: residue dials are hints, and obey the master bound -/



open GenericRecovery in
theorem solution(n : ℕ) :
    worstCost (oddResidues n) (fun x => x ^ 2 % 2 ^ (n + 3)) = 4 := by
  have hne : (oddResidues n).Nonempty := by
    refine ⟨1, ?_⟩
    simp only [oddResidues, Finset.mem_filter, mem_range]
    exact ⟨Nat.one_lt_two_pow (by omega), by trivial⟩
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    exact le_of_eq (cost_sqHint n u hu)
  · obtain ⟨u, hu⟩ := hne
    have hmem : (u ^ 2 % 2 ^ (n + 3)) ∈ (oddResidues n).image (fun x => x ^ 2 % 2 ^ (n + 3)) :=
      Finset.mem_image_of_mem _ hu
    have h := cost_le_worstCost (S := oddResidues n)
      (h := fun x => x ^ 2 % 2 ^ (n + 3)) hmem
    rwa [cost_sqHint n u hu] at h
