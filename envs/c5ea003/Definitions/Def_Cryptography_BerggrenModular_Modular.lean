-- Prove2me | Definitions.Def_Cryptography_BerggrenModular_Modular
-- name    : Cryptography_BerggrenModular_Modular
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:05:46.883677+00:00
-- url     : https://prove2.me/theorems/9918f77a-0287-4885-8eb6-f82bf43a467e
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenModular_Modular
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenModular.Modular`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenModular/Modular.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core

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

namespace Cryptography
namespace BerggrenModular

/-- A state of the Berggren system reduced modulo `m`. -/
abbrev TriM (m : ℕ) := ZMod m × ZMod m × ZMod m

/-- The Berggren moves acting on `(ℤ/m)³`. -/
def applyMoveM (m : ℕ) (i : Move) (w : TriM m) : TriM m :=
  match i with
  | .m1 => (w.1 - 2 * w.2.1 + 2 * w.2.2, 2 * w.1 - w.2.1 + 2 * w.2.2,
            2 * w.1 - 2 * w.2.1 + 3 * w.2.2)
  | .m2 => (w.1 + 2 * w.2.1 + 2 * w.2.2, 2 * w.1 + w.2.1 + 2 * w.2.2,
            2 * w.1 + 2 * w.2.1 + 3 * w.2.2)
  | .m3 => (-w.1 + 2 * w.2.1 + 2 * w.2.2, -2 * w.1 + w.2.1 + 2 * w.2.2,
            -2 * w.1 + 2 * w.2.1 + 3 * w.2.2)

/-- The inverse Berggren moves acting on `(ℤ/m)³`. -/
def invMoveM (m : ℕ) (i : Move) (w : TriM m) : TriM m :=
  match i with
  | .m1 => (w.1 + 2 * w.2.1 - 2 * w.2.2, -2 * w.1 - w.2.1 + 2 * w.2.2,
            -2 * w.1 - 2 * w.2.1 + 3 * w.2.2)
  | .m2 => (w.1 + 2 * w.2.1 - 2 * w.2.2, 2 * w.1 + w.2.1 - 2 * w.2.2,
            -2 * w.1 - 2 * w.2.1 + 3 * w.2.2)
  | .m3 => (-w.1 - 2 * w.2.1 + 2 * w.2.2, 2 * w.1 + w.2.1 - 2 * w.2.2,
            -2 * w.1 - 2 * w.2.1 + 3 * w.2.2)




/-- The Lorentz form modulo `m`. -/
def lorentzM (m : ℕ) (w : TriM m) : ZMod m := w.1 ^ 2 + w.2.1 ^ 2 - w.2.2 ^ 2


/-! ## Reduction is equivariant -/

/-- Reduce an integer state modulo `m`. -/
def redTri (m : ℕ) (v : Tri) : TriM m := ((v.1 : ZMod m), (v.2.1 : ZMod m), (v.2.2 : ZMod m))


/-- Apply a control word modulo `m`. -/
def applyWordM (m : ℕ) : List Move → TriM m → TriM m
  | [], w => w
  | i :: u, w => applyMoveM m i (applyWordM m u w)





/-! ## The classifier modulo `m` -/

/-- The canonical lift of a modular state, using representatives in `[0, m)`. -/
def liftTri (m : ℕ) [NeZero m] (w : TriM m) : Tri :=
  ((w.1.val : ℤ), (w.2.1.val : ℤ), (w.2.2.val : ℤ))

/-- The classifier as an observer of a modular state can only see it: it lifts the
residue canonically and runs the integer test. -/
def whichMoveMod (m : ℕ) [NeZero m] (w : TriM m) : Move := whichMove (liftTri m w)




/-- Iterating soundness: as long as the whole trajectory stays below the modulus,
modular seed recovery agrees with integer seed recovery. -/
def recoverMod (m : ℕ) [NeZero m] : ℕ → TriM m → List Move
  | 0, _ => []
  | n + 1, w => whichMoveMod m w :: recoverMod m n (invMoveM m (whichMoveMod m w) w)


/-! ## Sharpness: the classifier fails once the state wraps around -/



/-! ## Matrix form and the `B₂` discrete logarithm -/

/-- The vector attached to a modular state. -/
def vecOfM (m : ℕ) (w : TriM m) : Fin 3 → ZMod m := ![w.1, w.2.1, w.2.2]

/-- The Berggren matrices reduced modulo `m`. -/
def bergMatrixM (m : ℕ) (i : Move) : Matrix (Fin 3) (Fin 3) (ZMod m) :=
  (bergMatrix i).map (Int.cast)




end BerggrenModular
end Cryptography


