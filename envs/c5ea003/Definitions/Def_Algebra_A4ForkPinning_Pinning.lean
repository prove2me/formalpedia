-- Prove2me | Definitions.Def_Algebra_A4ForkPinning_Pinning
-- name    : Algebra_A4ForkPinning_Pinning
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:51.128313+00:00
-- url     : https://prove2.me/theorems/7e011539-f8a0-4ce4-8c90-ca11109c4fd6
-- title:
--   Aether Catalog definitions — Algebra_A4ForkPinning_Pinning
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.A4ForkPinning.Pinning`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/A4ForkPinning/Pinning.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_GroupA4
import Definitions.Def_Algebra_A4ForkPinning_Information
import Definitions.Def_Algebra_A4ForkPinning_Resolvent
/-
# The A₄ fork is cubic-pinned at `H(1/3)` — prime level

Putting the three previous files together at the level of a single prime.

The dial is the residue `p mod 9` (six coprime classes, equidistributed by
Dirichlet).  Class field theory for the cyclic cubic field `K = ℚ(ζ₉)⁺` of
conductor `9` (`Resolvent.lean`: `K` *is* the field of the Klein resolvent of
`x⁴ + 8x + 12`) says that the `V₄`-fork

`F₀(p) = [Frob p ∈ V₄] = [p is a cube mod 9] = [p ≡ ±1 mod 9]`

is a *deterministic function of the dial*, while Chebotarev makes the Frobenius
equidistributed in `A₄`, so that inside the `V₄`-fibre the identity has
conditional probability `1/|V₄| = 1/4` (`GroupA4.card_V4`).

What is proved here:

* `A4ForkPinning.info_mod9_V4_fork` — **`I(p mod 9 ; F₀) = H(1/3)` exactly**: the
  first *cubic* pinning, and the same value as for the abelian cyclic cubic;
* `A4ForkPinning.hb_third_bounds` — `0.918 < H(1/3) < 0.919`, matching the
  measured `0.9188` of the experiment (verified by integer power comparisons);
* `A4ForkPinning.info_mod9_identity_fork` — **the exact leakage law for
  `F₁ = [Frob = e]`**: `I = H(1/12) - (1/3)·H(1/4)`, strictly between `0` and
  `H(F₁)`: the identity fork is neither pinned nor flat;
* `A4ForkPinning.info_mod5_flat` — the coprime dial mod `5` is flat, `I = 0`;
* `A4ForkPinning.info_mod9_V4_fork_is_maximal` — `F₀` saturates the channel while
  `F₁` cannot: a formal separation of the two regimes.
-/

namespace A4ForkPinning

open Real Finset

/-! ## Numerics for `H(1/3)` and `H(1/4)` -/







/-! ## The mod-9 dial -/

/-- The six residue classes coprime to `9`. -/
def res6 : Fin 6 → ZMod 9 := ![1, 2, 4, 5, 7, 8]




/-- Dirichlet: the six classes are equidistributed. -/
noncomputable def w6 : Fin 6 → ℝ := fun _ => 1 / 6



/-- The `V₄`-fork read off the dial: `F₀(p) = [p is a cube mod 9]`.  By class field
theory for the conductor-`9` cyclic cubic this is a *deterministic* function of the
residue class. -/
noncomputable def F0 : Fin 6 → ℝ := fun i => if chi9 (res6 i) = 0 then 1 else 0





/-! ## Chebotarev rates from the group side -/



/-! ## The identity fork leaks -/

/-- The identity fork `F₁ = [Frob = e]`.  Given `Frob ∈ V₄` (which the dial *does*
determine) the Frobenius is equidistributed in `V₄`, a group of order `4`
(`card_V4`), so the conditional rate is `(1/4)·F₀`. -/
noncomputable def F1 : Fin 6 → ℝ := fun i => (1 / 4) * F0 i





/-! ## Minimality of the conductor: the dial mod 3 is flat -/

/-- Units mod `9` lying over a given class mod `3`. -/
def unitsOverMod3 (r : ℕ) : ℕ :=
  (univ.filter (fun x : ZMod 9 => IsUnit x ∧ x.val % 3 = r)).card

/-- Cubes mod `9` lying over a given class mod `3`. -/
def cubesOverMod3 (r : ℕ) : ℕ :=
  (univ.filter (fun x : ZMod 9 => IsUnit x ∧ x.val % 3 = r ∧ chi9 x = 0)).card





/-- The two classes mod `3` that a prime `p ∤ 3` can occupy. -/
def mod3class : Fin 2 → ℕ := ![1, 2]

noncomputable def w2 : Fin 2 → ℝ := fun _ => 1 / 2


/-- Reading the `V₄`-fork through the dial `p mod 3` gives the constant rate `1/3`:
each class mod `3` contains exactly one cube among its three units mod `9`. -/
noncomputable def F0mod3 : Fin 2 → ℝ := fun _ => 1 / 3



/-! ## Flatness of a coprime dial mod 5 -/

/-- The four residue classes coprime to `5`, again equidistributed. -/
noncomputable def w4 : Fin 4 → ℝ := fun _ => 1 / 4


/-- Reading the `V₄`-fork through a dial mod `5` (a modulus prime to the conductor)
gives the constant conditional rate `1/3`. -/
noncomputable def F0mod5 : Fin 4 → ℝ := fun _ => 1 / 3


end A4ForkPinning


