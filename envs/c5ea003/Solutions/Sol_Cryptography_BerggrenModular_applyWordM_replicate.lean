-- Prove2me | solution 1 for Cryptography.BerggrenModular.applyWordM_replicate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:14:41.934744+00:00
-- url     : https://prove2.me/submissions/e015d96f-1e13-41f7-b12c-8fabe100bdef

-- Sol generated from Cryptography/BerggrenModular/Modular.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Modular

/-!
# Berggren moves on `(ℤ/m)³`

We push the Berggren moves through the reduction map `ℤ³ → (ℤ/m)³` and study
what survives.

## Main results

* `redTri_applyMove`, `redTri_applyWord` — reduction is equivariant: the modular
  dynamics is a genuine quotient of the integer dynamics.
* `applyMoveM_bijective` — every modular move is a bijection of `(ℤ/m)³`
  (the state map itself loses nothing; all loss comes from wrap-around).
* `lorentzM_applyMoveM` — the Lorentz form `a²+b²−c²` is still invariant mod `m`.
* `whichMoveMod_redTri` — **the classifier remains sound modulo `m`**: as long as
  the observed state has not wrapped around (`hypotenuse < m`), the canonical
  lift of the residue is the true state and `whichMove` returns the true last move.
* `whichMoveMod_not_sound_mod_seven` — and this hypothesis is sharp: an explicit
  failure at `m = 7`.
* `vecOfM_iterate_applyMoveM` — iterating the move `B₂` mod `m` is exactly
  multiplication by the matrix power `B₂^t` over `ℤ/m`, which is what makes the
  seed-recovery problem for `B₂`-only words a discrete-logarithm problem.
-/

open Cryptography
open BerggrenModular









/-! ## Reduction is equivariant -/





@[simp] theorem applyWordM_cons (m : ℕ) (i : Move) (u : List Move) (w : TriM m) :
    applyWordM m (i :: u) w = applyMoveM m i (applyWordM m u w) := rfl



/-! ## The classifier modulo `m` -/








/-! ## Sharpness: the classifier fails once the state wraps around -/



/-! ## Matrix form and the `B₂` discrete logarithm -/







open Cryptography.BerggrenModular in
theorem solution(m : ℕ) (i : Move) (t : ℕ) (w : TriM m) :
    applyWordM m (List.replicate t i) w = (applyMoveM m i)^[t] w := by
  induction t generalizing w with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, applyWordM_cons, ih]
      exact (Function.iterate_succ_apply' _ _ _).symm
