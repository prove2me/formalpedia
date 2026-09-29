-- Prove2me | solution 1 for Cryptography.BerggrenModular.recoverMod_applyWordM
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:29:31.080367+00:00
-- url     : https://prove2.me/submissions/46b5a11b-7548-468d-ab64-e6d6be73a96a

-- Sol generated from Cryptography/BerggrenModular/Modular.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_cons
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_valid
import Theorems.Thm_Cryptography_BerggrenModular_invMoveM_applyMoveM
import Theorems.Thm_Cryptography_BerggrenModular_redTri_applyMove
import Theorems.Thm_Cryptography_BerggrenModular_whichMoveMod_redTri

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








/-! ## Sharpness: the classifier fails once the state wraps around -/



/-! ## Matrix form and the `B₂` discrete logarithm -/







open Cryptography.BerggrenModular in
theorem solution{m : ℕ} [NeZero m] (u : List Move) {v : Tri} (hv : Valid v)
    (hb : ∀ s : List Move, s <:+ u → (applyWord s v).2.2 < m) :
    recoverMod m u.length (redTri m (applyWord u v)) = u := by
  induction u with
  | nil => rfl
  | cons i rest ih =>
      have hu : Valid (applyWord rest v) := applyWord_valid rest hv
      have hbi : (applyMove i (applyWord rest v)).2.2 < m := hb (i :: rest) (List.suffix_refl _)
      have hstep : whichMoveMod m (redTri m (applyWord (i :: rest) v)) = i := by
        rw [applyWord_cons]; exact whichMoveMod_redTri i hu hbi
      simp only [List.length_cons, recoverMod]
      rw [hstep]
      have hinv : invMoveM m i (redTri m (applyWord (i :: rest) v))
          = redTri m (applyWord rest v) := by
        rw [applyWord_cons, redTri_applyMove, invMoveM_applyMoveM]
      rw [hinv, ih (fun s hs => hb s (hs.trans (List.suffix_cons i rest)))]
