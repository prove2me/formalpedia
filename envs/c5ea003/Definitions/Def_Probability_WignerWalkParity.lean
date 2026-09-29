-- Prove2me | Definitions.Def_Probability_WignerWalkParity
-- name    : Probability_WignerWalkParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:58.304157+00:00
-- url     : https://prove2.me/theorems/38eebb3f-0d97-4b09-8add-be5a0bc17feb
-- title:
--   Aether Catalog definitions — Probability_WignerWalkParity
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerWalkParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerWalkParity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The sign-flip involution at arbitrary order: parity of edge multiplicities

`Probability.WignerRademacherEnsemble` kills the expectation of a closed **4**-walk
whose first edge is traversed exactly once, by flipping the Rademacher variable
attached to that edge.  This file isolates the mechanism and proves it at
**arbitrary order**, for an arbitrary walk of arbitrary length:

* `RademacherWigner.prod_entry_flipEdge` — flipping the sign of one edge `p`
  multiplies the product of matrix entries along a walk by `(-1)^c`, where `c` is
  the number of steps of the walk that traverse `p`;
* `RademacherWigner.expect_prod_entry_eq_zero` — hence, if some edge is traversed
  an **odd** number of times, the ensemble average of the walk monomial is `0`.

This is the exact combinatorial reason why only walks whose edge multiset has all
multiplicities even survive in `E [ tr W^m ]`, which is the input to the
moment-method proof of the semicircle law at every order.  Two instantiations are
given: the length-four case, which reproves
`RademacherWigner.expect_term_eq_zero`, and the length-six case, which is the first
case not covered by the earlier files (and the first step towards the exact sixth
trace moment).
-/

open Matrix BigOperators Finset

namespace RademacherWigner

variable {N : ℕ}

/-! ### Edge multiplicities along a walk -/

/-- The number of the first `m` steps of the walk `w` that traverse the edge `p`. -/
noncomputable def edgeCount (m : ℕ) (w : ℕ → Fin N) (p : Fin N × Fin N) : ℕ :=
  ((Finset.range m).filter fun t => edgeOf (w t) (w (t + 1)) = p).card

/-- The monomial attached to the first `m` steps of the walk `w`. -/
def walkProd (g : Config N) (m : ℕ) (w : ℕ → Fin N) : ℝ :=
  ∏ t ∈ Finset.range m, entry g (w t) (w (t + 1))




/-! ### The closed four-walk, revisited -/

/-- The closed 4-walk `i → j → k → l → i`, as a `4`-periodic function on `ℕ`. -/
def walk4 (i j k l : Fin N) : ℕ → Fin N := fun t =>
  if t % 4 = 0 then i else if t % 4 = 1 then j else if t % 4 = 2 then k else l




/-! ### The closed six-walk -/

/-- The closed 6-walk `i → j → k → l → m → n → i`, as a `6`-periodic function. -/
def walk6 (i j k l m n : Fin N) : ℕ → Fin N := fun t =>
  if t % 6 = 0 then i else if t % 6 = 1 then j else if t % 6 = 2 then k
  else if t % 6 = 3 then l else if t % 6 = 4 then m else n




end RademacherWigner


