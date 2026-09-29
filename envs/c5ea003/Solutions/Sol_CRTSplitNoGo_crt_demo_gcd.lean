-- Prove2me | solution 1 for CRTSplitNoGo.crt_demo_gcd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:32:41.568893+00:00
-- url     : https://prove2.me/submissions/ec7f5407-e598-4faa-952c-4f9b2493f696

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoBounds
open CRTSplitNoGo Polynomial in
theorem solution :
    Int.gcd (polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23) ((341371 : ℕ) : ℤ) = 631 := by
  -- the orbit reduces mod `341371` to the orbit of `z ↦ z² + 1` in `ZMod 341371`
  have hcast : ∀ n : ℕ, ((polyOrbit (X ^ 2 + 1) 2 n : ℤ) : ZMod 341371)
      = (fun z : ZMod 341371 => z ^ 2 + 1)^[n] 2 := by
    intro n
    induction n with
    | zero => simp [polyOrbit]
    | succ n ih =>
      have e : polyOrbit (X ^ 2 + 1) 2 (n + 1)
          = (polyOrbit (X ^ 2 + 1) 2 n) ^ 2 + 1 := by
        simp only [polyOrbit]
        rw [Function.iterate_succ_apply']
        simp
      rw [e, Function.iterate_succ_apply', ← ih]
      push_cast
      rfl
  -- the reduced orbit is a finite computation
  have hcomp : (fun z : ZMod 341371 => z ^ 2 + 1)^[36] 2
      - (fun z : ZMod 341371 => z ^ 2 + 1)^[23] 2 = 133141 := by
    decide +kernel
  have hval : ((polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23 : ℤ) : ZMod 341371)
      = 133141 := by
    push_cast
    rw [hcast, hcast, hcomp]
  have hmod : (polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23) % ((341371 : ℕ) : ℤ)
      = 133141 := by
    rw [← ZMod.val_intCast, hval]
    rfl
  rw [← Int.gcd_emod, hmod]
  rfl
