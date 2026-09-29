-- Prove2me | solution 1 for Cryptography.BerggrenModular.redTri_applyWord
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:29:31.587246+00:00
-- url     : https://prove2.me/submissions/85f191d9-d5cd-44ce-9ccd-9774b2e50713

-- Sol generated from Cryptography/BerggrenModular/Modular.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_cons
import Theorems.Thm_Cryptography_BerggrenModular_redTri_applyMove

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
theorem solution(m : ℕ) (u : List Move) (v : Tri) :
    redTri m (applyWord u v) = applyWordM m u (redTri m v) := by
  induction u with
  | nil => rfl
  | cons i rest ih => rw [applyWord_cons, redTri_applyMove, ih, applyWordM_cons]
