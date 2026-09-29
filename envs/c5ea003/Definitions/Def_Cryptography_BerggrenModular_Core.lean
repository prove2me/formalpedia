-- Prove2me | Definitions.Def_Cryptography_BerggrenModular_Core
-- name    : Cryptography_BerggrenModular_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:05:07.396464+00:00
-- url     : https://prove2.me/theorems/52b30f0c-3577-448b-b4fd-3b46e903bcc6
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenModular_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenModular.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenModular/Core.lean by skeleton subtraction
import Mathlib

/-!
# Berggren moves over `ℤ`: the exact move classifier and free-monoid seed recovery

This file is the integer-side foundation for the modular study carried out in
`Cryptography.BerggrenModular.Modular` and
`Cryptography.BerggrenModular.Hardness`.

The three Berggren (Barning–Hall) moves `B₁, B₂, B₃` act on integer triples and
preserve the Lorentz form `a² + b² − c²`; on the cone of positive Pythagorean
triples they generate a ternary tree rooted at `(3,4,5)`.

The central object here is an **exact, purely linear classifier**

```
whichMove (a,b,c) = if 5a < 3c then B₁ else if 5a < 4c then B₂ else B₃
```

which reads off, from a single child state, *which* move produced it.  The
thresholds `3/5` and `4/5` are the images of the ratio tests `m < 2n`,
`2n < m < 3n`, `m > 3n` in the Euclid parametrisation `a = m²−n²`, `b = 2mn`,
`c = m²+n²`, transported through `m/n = √((c+a)/(c−a))`.

## Main results

* `whichMove_applyMove` — soundness *and* completeness of the classifier over `ℤ`.
* `applyMove_valid` — the positive Pythagorean cone is invariant.
* `invMove_applyMove` — each move is inverted by an explicit integer matrix.
* `recover_applyWord` — a **linear-time seed-recovery algorithm** over `ℤ`:
  the control word is recovered exactly from a single observed state.
* `applyWord_injective` — the Berggren monoid acts freely on the cone
  (so the length-`k` search space really has `3^k` distinct states).
-/

namespace Cryptography
namespace BerggrenModular

/-! ## Moves -/

/-- The three Berggren moves. -/
inductive Move : Type
  | m1 | m2 | m3
  deriving DecidableEq, Repr, Fintype


/-- An integer triple. -/
abbrev Tri := ℤ × ℤ × ℤ

/-- The Berggren move `B₁`, `B₂`, `B₃` acting on integer triples. -/
def applyMove (i : Move) (v : Tri) : Tri :=
  match i with
  | .m1 => (v.1 - 2 * v.2.1 + 2 * v.2.2, 2 * v.1 - v.2.1 + 2 * v.2.2,
            2 * v.1 - 2 * v.2.1 + 3 * v.2.2)
  | .m2 => (v.1 + 2 * v.2.1 + 2 * v.2.2, 2 * v.1 + v.2.1 + 2 * v.2.2,
            2 * v.1 + 2 * v.2.1 + 3 * v.2.2)
  | .m3 => (-v.1 + 2 * v.2.1 + 2 * v.2.2, -2 * v.1 + v.2.1 + 2 * v.2.2,
            -2 * v.1 + 2 * v.2.1 + 3 * v.2.2)

/-- The inverse Berggren moves `Bᵢ⁻¹ = Q Bᵢᵀ Q` with `Q = diag(1,1,-1)`. -/
def invMove (i : Move) (v : Tri) : Tri :=
  match i with
  | .m1 => (v.1 + 2 * v.2.1 - 2 * v.2.2, -2 * v.1 - v.2.1 + 2 * v.2.2,
            -2 * v.1 - 2 * v.2.1 + 3 * v.2.2)
  | .m2 => (v.1 + 2 * v.2.1 - 2 * v.2.2, 2 * v.1 + v.2.1 - 2 * v.2.2,
            -2 * v.1 - 2 * v.2.1 + 3 * v.2.2)
  | .m3 => (-v.1 - 2 * v.2.1 + 2 * v.2.2, 2 * v.1 + v.2.1 - 2 * v.2.2,
            -2 * v.1 - 2 * v.2.1 + 3 * v.2.2)

/-- The Lorentz form of signature `(2,1)`. -/
def lorentz (v : Tri) : ℤ := v.1 ^ 2 + v.2.1 ^ 2 - v.2.2 ^ 2






/-! ## The positive Pythagorean cone -/

/-- A *valid* state: a strictly positive Pythagorean triple. -/
def Valid (v : Tri) : Prop :=
  0 < v.1 ∧ 0 < v.2.1 ∧ 0 < v.2.2 ∧ v.1 ^ 2 + v.2.1 ^ 2 = v.2.2 ^ 2






/-! ## The exact linear classifier -/

/-- **The Berggren move classifier.**  Given a child state `(a,b,c)` it returns the
unique move that produced it.  The test is purely linear in the state. -/
def whichMove (v : Tri) : Move :=
  if 5 * v.1 < 3 * v.2.2 then .m1 else if 5 * v.1 < 4 * v.2.2 then .m2 else .m3



/-! ## Words, orbits and seed recovery -/

/-- Apply a control word.  The head of the list is the **last** move applied. -/
def applyWord : List Move → Tri → Tri
  | [], v => v
  | i :: w, v => applyMove i (applyWord w v)






/-- **Seed recovery over `ℤ`.**  Peel off `n` moves, each step costing one
comparison and one linear map. -/
def recover : ℕ → Tri → List Move
  | 0, _ => []
  | n + 1, v => whichMove v :: recover n (invMove (whichMove v) v)



/-- The classical root of the Berggren tree. -/
def root : Tri := (3, 4, 5)


/-! ## Matrix formulation -/

/-- The Berggren moves as `3×3` integer matrices. -/
def bergMatrix : Move → Matrix (Fin 3) (Fin 3) ℤ
  | .m1 => !![1, -2, 2; 2, -1, 2; 2, -2, 3]
  | .m2 => !![1, 2, 2; 2, 1, 2; 2, 2, 3]
  | .m3 => !![-1, 2, 2; -2, 1, 2; -2, 2, 3]

/-- The vector attached to a triple. -/
def vecOf (v : Tri) : Fin 3 → ℤ := ![v.1, v.2.1, v.2.2]



end BerggrenModular
end Cryptography


