-- Prove2me | Theorems.Thm_Cryptography_BerggrenModular_vecOfM_iterate_applyMoveM
-- name    : Cryptography.BerggrenModular.vecOfM_iterate_applyMoveM
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:39:53.788767+00:00
-- url     : https://prove2.me/theorems/973252fd-836d-4a1e-ab2a-1ecb91814223
-- title:
--   Iterating a single move is a matrix power.
-- statement:
--   **Iterating a single move is a matrix power.**  Consequently, recovering the
--   number of `B₂`-steps from an observed modular state is literally a discrete
--   logarithm problem for the matrix `B₂` in `GL₃(ℤ/m)`.
--
--   ```lean
--   theorem Cryptography.BerggrenModular.vecOfM_iterate_applyMoveM(m : ℕ) (i : Move) (t : ℕ) (w : TriM m) :
--       vecOfM m ((applyMoveM m i)^[t] w) = ((bergMatrixM m i) ^ t).mulVec (vecOfM m w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenModular/Modular.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenModular/Modular.lean#L200

-- Thm stub generated from Cryptography/BerggrenModular/Modular.lean
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

theorem Cryptography.BerggrenModular.vecOfM_iterate_applyMoveM(m : ℕ) (i : Move) (t : ℕ) (w : TriM m) :
    vecOfM m ((applyMoveM m i)^[t] w) = ((bergMatrixM m i) ^ t).mulVec (vecOfM m w) := by sorry
