-- Prove2me | solution 1 for Cryptography.BerggrenModular.liftTri_redTri
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:25:34.046557+00:00
-- url     : https://prove2.me/submissions/b597de3a-8c0c-455f-b5c2-d7138795d381

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








/-! ## The classifier modulo `m` -/



theorem liftZ_red {m : ℕ} [NeZero m] {a : ℤ} (h0 : 0 ≤ a) (h1 : a < m) :
    (((a : ZMod m).val : ℤ)) = a := by
  rw [ZMod.val_intCast]; exact Int.emod_eq_of_lt h0 h1





/-! ## Sharpness: the classifier fails once the state wraps around -/



/-! ## Matrix form and the `B₂` discrete logarithm -/







open Cryptography.BerggrenModular in
theorem solution{m : ℕ} [NeZero m] {v : Tri} (h1 : 0 ≤ v.1) (h2 : 0 ≤ v.2.1)
    (h3 : 0 ≤ v.2.2) (b1 : v.1 < m) (b2 : v.2.1 < m) (b3 : v.2.2 < m) :
    liftTri m (redTri m v) = v := by
  simp only [liftTri, redTri]
  refine Prod.ext (liftZ_red h1 b1) (Prod.ext (liftZ_red h2 b2) (liftZ_red h3 b3))
