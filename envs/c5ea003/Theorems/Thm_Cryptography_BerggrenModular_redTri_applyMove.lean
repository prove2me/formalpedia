-- Prove2me | Theorems.Thm_Cryptography_BerggrenModular_redTri_applyMove
-- name    : Cryptography.BerggrenModular.redTri_applyMove
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:39:12.648481+00:00
-- url     : https://prove2.me/theorems/a4f5d5c9-c12f-4603-a74b-f44986479e4a
-- title:
--   RedTri applyMove
-- statement:
--   Formal statement of `Cryptography.BerggrenModular.redTri_applyMove` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Cryptography.BerggrenModular.redTri_applyMove(m : ℕ) (i : Move) (v : Tri) :
--       redTri m (applyMove i v) = applyMoveM m i (redTri m v) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenModular/Modular.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenModular/Modular.lean#L77

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

theorem Cryptography.BerggrenModular.redTri_applyMove(m : ℕ) (i : Move) (v : Tri) :
    redTri m (applyMove i v) = applyMoveM m i (redTri m v) := by sorry
