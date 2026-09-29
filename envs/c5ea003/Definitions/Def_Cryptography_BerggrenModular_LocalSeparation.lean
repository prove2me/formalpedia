-- Prove2me | Definitions.Def_Cryptography_BerggrenModular_LocalSeparation
-- name    : Cryptography_BerggrenModular_LocalSeparation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:08:12.64208+00:00
-- url     : https://prove2.me/theorems/4bc4e70a-b243-4357-860d-9bb9d48150df
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenModular_LocalSeparation
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenModular.LocalSeparation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenModular/LocalSeparation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Definitions.Def_Cryptography_BerggrenModular_SilverOrbit

/-!
# Local separation of the three moves modulo `m`

`Cryptography.BerggrenModular.Modular` shows that the *absolute* classifier — the
one that sees only the child state — stays sound modulo `m` exactly while the
state has not wrapped around.  Here we analyse the **relative** classifier, which
sees the parent as well.  It is sound modulo `m` precisely when the three children
of the parent are pairwise distinct, and we compute exactly when that happens:

```
B₁w − B₂w = (−4b, −2b, −4b),
B₂w − B₃w = ( 2a,  4a,  4a),
B₁w − B₃w = (2a − 4b, 4a − 2b, 4a − 4b).
```

So the branching is visible modulo `m` iff `2a`, `2b` and `2a − 4b` are nonzero in
`ℤ/m`.  Two consequences are worth isolating:

* `whichMoveRel_sound` — the relative classifier is sound (and complete) under
  exactly those three nondegeneracy conditions;
* `applyMoveM_two_eq_id` — modulo `2` all three Berggren moves are the identity,
  so the dynamics collapses completely and no classifier of any kind can work.
  This is the extreme case of the information loss quantified in
  `Cryptography.BerggrenModular.Hardness`.
-/

namespace Cryptography
namespace BerggrenModular

variable {m : ℕ}

/-! ## The three difference vectors -/




/-! ## Pairwise distinctness of the children -/




/-- A modular state whose three children are pairwise distinguishable. -/
def Separated (w : TriM m) : Prop :=
  (2 : ZMod m) * w.1 ≠ 0 ∧ (2 : ZMod m) * w.2.1 ≠ 0 ∧ (2 : ZMod m) * w.1 - 4 * w.2.1 ≠ 0


/-! ## The relative classifier -/

/-- The relative classifier: given the parent `w` and the observed child `x`, name
the move.  Purely algebraic — no order, no lifting. -/
def whichMoveRel (m : ℕ) (w x : TriM m) : Option Move :=
  if x = applyMoveM m Move.m1 w then some Move.m1
  else if x = applyMoveM m Move.m2 w then some Move.m2
  else if x = applyMoveM m Move.m3 w then some Move.m3
  else none



/-! ## The degenerate modulus -/





end BerggrenModular
end Cryptography


