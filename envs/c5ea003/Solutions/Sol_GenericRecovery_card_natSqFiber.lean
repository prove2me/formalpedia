-- Prove2me | solution 1 for GenericRecovery.card_natSqFiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:39:27.352548+00:00
-- url     : https://prove2.me/submissions/63935a5a-e2fd-495b-8c1e-d65a86302d48

-- Sol generated from Combinatorics/GenericRecoveryHintSharpness.lean
import Mathlib
import Definitions.Def_Combinatorics_DialThresholdNoAmplification
import Definitions.Def_Combinatorics_GenericRecoveryHintSharpness
import Definitions.Def_Combinatorics_GenericRecoveryHintTaxonomy
import Theorems.Thm_GenericRecovery_card_sq_fiber_eq_four
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








/-! ## 4.  Bridge: residue dials are hints, and obey the master bound -/



open GenericRecovery in
theorem solution(n u : ℕ) (hu : u % 2 = 1) :
    #{x ∈ range (2 ^ (n + 3)) | x ^ 2 % 2 ^ (n + 3) = u ^ 2 % 2 ^ (n + 3)} = 4 := by
  have huZ : Odd (u : ℤ) := by
    obtain ⟨k, hk⟩ : ∃ k, u = 2 * k + 1 := ⟨u / 2, by omega⟩
    exact ⟨(k : ℤ), by rw [hk]; push_cast; ring⟩
  have hcast : ∀ x : ℕ, (x ^ 2 % 2 ^ (n + 3) = u ^ 2 % 2 ^ (n + 3)) ↔
      ((x : ZMod (2 ^ (n + 3))) ^ 2 = ((u : ℤ) : ZMod (2 ^ (n + 3))) ^ 2) := by
    intro x
    have h := ZMod.natCast_eq_natCast_iff' (x ^ 2) (u ^ 2) (2 ^ (n + 3))
    push_cast at h
    have hu2 : (((u : ℤ)) : ZMod (2 ^ (n + 3))) = ((u : ℕ) : ZMod (2 ^ (n + 3))) := by
      push_cast; ring
    rw [hu2]
    exact h.symm
  rw [← card_sq_fiber_eq_four n u huZ]
  refine Finset.card_nbij (fun x => (x : ZMod (2 ^ (n + 3)))) ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq, mem_range, mem_univ, true_and] at hx ⊢
    exact (hcast x).mp hx.2
  · intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hx hy
    have hxy' : ((x : ℕ) : ZMod (2 ^ (n + 3))) = ((y : ℕ) : ZMod (2 ^ (n + 3))) := hxy
    have hx' : (x : ZMod (2 ^ (n + 3))).val = x := ZMod.val_natCast_of_lt hx.1
    have hy' : (y : ZMod (2 ^ (n + 3))).val = y := ZMod.val_natCast_of_lt hy.1
    rw [← hx', ← hy', hxy']
  · intro z hz
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hz
    refine ⟨z.val, ?_, ?_⟩
    · simp only [coe_filter, Set.mem_setOf_eq, mem_range]
      refine ⟨ZMod.val_lt z, ?_⟩
      refine (hcast z.val).mpr ?_
      rwa [ZMod.natCast_val, ZMod.cast_id]
    · simp [ZMod.natCast_val, ZMod.cast_id]
