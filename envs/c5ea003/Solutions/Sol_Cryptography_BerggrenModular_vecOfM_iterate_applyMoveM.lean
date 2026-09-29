-- Prove2me | solution 1 for Cryptography.BerggrenModular.vecOfM_iterate_applyMoveM
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:29:33.854673+00:00
-- url     : https://prove2.me/submissions/2444deb2-38e4-4e52-af87-bfe216ec3fab

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








/-! ## Sharpness: the classifier fails once the state wraps around -/



/-! ## Matrix form and the `B₂` discrete logarithm -/



theorem vecOfM_applyMoveM (m : ℕ) (i : Move) (w : TriM m) :
    vecOfM m (applyMoveM m i w) = (bergMatrixM m i).mulVec (vecOfM m w) := by
  cases i <;>
    · funext k
      fin_cases k <;>
        simp [vecOfM, applyMoveM, bergMatrixM, bergMatrix, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three] <;>
        ring




open Cryptography.BerggrenModular in
theorem solution(m : ℕ) (i : Move) (t : ℕ) (w : TriM m) :
    vecOfM m ((applyMoveM m i)^[t] w) = ((bergMatrixM m i) ^ t).mulVec (vecOfM m w) := by
  induction t generalizing w with
  | zero => simp [Matrix.one_mulVec]
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, vecOfM_applyMoveM, pow_succ']
      rw [Matrix.mulVec_mulVec]
      have hcomm : bergMatrixM m i ^ n * bergMatrixM m i
          = bergMatrixM m i * bergMatrixM m i ^ n := by
        rw [← pow_succ, ← pow_succ']
      rw [hcomm]
