-- Prove2me | solution 1 for CRTSplitNoGo.crt_demo_first_reveal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:24:43.1023+00:00
-- url     : https://prove2.me/submissions/3679ef53-46b1-4930-85ee-a0abf9bd2cb4

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoBounds
open CRTSplitNoGo Polynomial in
theorem solution (s t : ℕ) (hst : s < t) (ht : t ≤ 35) :
    ¬ RevealsFactor (631 * 541) (polyOrbit (X ^ 2 + 1) 2 t - polyOrbit (X ^ 2 + 1) 2 s) := by
  rw [show (631 * 541 : ℕ) = 341371 by norm_num]
  -- the orbit reduced mod `341371`, computed in `ℕ`
  let r : ℕ → ℕ := fun n => (fun z : ℕ => (z ^ 2 + 1) % 341371)^[n] 2
  have hr_succ : ∀ n, r (n + 1) = (r n ^ 2 + 1) % 341371 := fun n =>
    Function.iterate_succ_apply' _ n 2
  have hr_lt : ∀ n, r n < 341371 := by
    intro n
    cases n with
    | zero => show 2 < 341371; norm_num
    | succ n => rw [hr_succ]; exact Nat.mod_lt _ (by norm_num)
  have hcast : ∀ n : ℕ, ((polyOrbit (X ^ 2 + 1) 2 n : ℤ) : ZMod 341371) = ((r n : ℕ) : ZMod 341371) := by
    intro n
    induction n with
    | zero => simp [polyOrbit, r]
    | succ n ih =>
      have e : polyOrbit (X ^ 2 + 1) 2 (n + 1) = (polyOrbit (X ^ 2 + 1) 2 n) ^ 2 + 1 := by
        simp only [polyOrbit]
        rw [Function.iterate_succ_apply']
        simp
      rw [e, hr_succ, ZMod.natCast_mod]
      push_cast
      rw [ih]
  -- the difference mod `341371`
  have hdiff : ((polyOrbit (X ^ 2 + 1) 2 t - polyOrbit (X ^ 2 + 1) 2 s : ℤ) : ZMod 341371)
      = ((r t + 341371 - r s : ℕ) : ZMod 341371) := by
    push_cast
    rw [hcast, hcast, Nat.cast_sub (by have := hr_lt s; omega)]
    push_cast
    rw [show (341371 : ZMod 341371) = 0 by decide]
    ring
  have hmod : (polyOrbit (X ^ 2 + 1) 2 t - polyOrbit (X ^ 2 + 1) 2 s) % ((341371 : ℕ) : ℤ)
      = (((r t + 341371 - r s) % 341371 : ℕ) : ℤ) := by
    rw [← ZMod.val_intCast, hdiff, ZMod.val_natCast]
  -- a finite check over all `s < t ≤ 35`
  have hcheck : ∀ t < 36, ∀ s < t,
      ¬ (1 < Nat.gcd ((r t + 341371 - r s) % 341371) 341371 ∧
        Nat.gcd ((r t + 341371 - r s) % 341371) 341371 < 341371) := by
    decide +kernel
  unfold RevealsFactor
  rw [← Int.gcd_emod, hmod, Int.gcd_natCast_natCast]
  exact hcheck t (by omega) s hst
