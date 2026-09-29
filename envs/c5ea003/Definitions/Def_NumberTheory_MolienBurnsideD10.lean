-- Prove2me | Definitions.Def_NumberTheory_MolienBurnsideD10
-- name    : NumberTheory_MolienBurnsideD10
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:28.029583+00:00
-- url     : https://prove2.me/theorems/388d40df-b6ee-4717-ae00-076b7c042249
-- title:
--   Aether Catalog definitions — NumberTheory_MolienBurnsideD10
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.MolienBurnsideD10`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/MolienBurnsideD10.lean by skeleton subtraction
import Mathlib

/-!
# Conjecture D10: is the Molien invariant exactly the Burnside mark vector modulo scaling?

For a finite group `G` acting on a finite set `X` there are two classical invariants.

* the **Burnside mark vector** `H ↦ markOn X H = |X^H|`, indexed by the subgroups of `G`;
* the **Molien invariant** `H ↦ molien X H = (1/|H|) ∑_{h ∈ H} |X^h|`, the subgroup-wise
  average of the permutation character (equivalently, by Burnside's lemma, the number of
  `H`-orbits, equivalently the constant term data of the Molien series of the permutation
  representation restricted to `H`).

Conjecture D10 asserts that these two invariants agree up to a scalar.  This file settles
the conjecture:

* **positive half** (`molien_eq_avgMarks`): the Molien invariant is always a *linear image*
  of the mark vector — it is the average over `h ∈ H` of the marks at the cyclic subgroups
  `⟨h⟩`.  Hence the mark vector determines the Molien invariant.
* **sharp positive result** (`markOn_eq_of_fixCount_eq_of_cyclic`): if every subgroup of `G`
  is cyclic (e.g. `G` cyclic), the Molien invariant conversely determines the whole mark
  vector *on the nose* (scaling factor `1`).
* **negative half** (`D10_false`): for the Klein four group `V = (ℤ/2)²` there are two
  `V`-sets with *identical* Molien invariants at every subgroup whose mark vectors are not
  proportional.  So Conjecture D10 is **false** in general, and the cyclic hypothesis above
  is exactly the boundary of its validity.

Along the way we prove the structural comparison `markOn ≤ molien` with the equality case
(`molien_eq_markOn_iff`), Burnside's orbit-counting identity in this normalisation
(`molien_eq_card_orbits`) and the resulting arithmetic divisibility
`|H| ∣ ∑_{h ∈ H} |X^h|`.
-/

namespace D10

open Finset MulAction

section Defs

variable {G : Type*} [Group G]

/-- The number of points of `X` fixed by the single element `g`, i.e. the value at `g`
of the permutation character of `X`. -/
def fixCount (X : Type*) [MulAction G X] [Fintype X] [DecidableEq X] (g : G) : ℕ :=
  (univ.filter fun x : X => g • x = x).card

/-- The **Burnside mark** of the `G`-set `X` at the subgroup `H`: the number of `H`-fixed
points of `X`. -/
def markOn (X : Type*) [MulAction G X] [Fintype X] [DecidableEq X]
    (H : Subgroup G) [Fintype H] : ℕ :=
  (univ.filter fun x : X => ∀ h : H, (h : G) • x = x).card

/-- The **Molien invariant** of the `G`-set `X` at the subgroup `H`: the average number of
fixed points of the elements of `H`. -/
def molien (X : Type*) [MulAction G X] [Fintype X] [DecidableEq X]
    (H : Subgroup G) [Fintype H] : ℚ :=
  (∑ h : H, (fixCount X (h : G) : ℚ)) / (Fintype.card H : ℚ)

end Defs

section Basic

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] [Fintype X] [DecidableEq X]







end Basic

section Molien

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] [Fintype X] [DecidableEq X]












end Molien

section Comparison

variable {G : Type*} [Group G] {X Y : Type*}
  [MulAction G X] [Fintype X] [DecidableEq X] [MulAction G Y] [Fintype Y] [DecidableEq Y]





end Comparison

section KleinCounterexample

/-! ### The Klein four group counterexample

Let `V = ℤ/2 × ℤ/2` (written multiplicatively).  Its three subgroups of index two are the
kernels of the three surjections `χ₀(a,b) = a`, `χ₁(a,b) = b`, `χ₂(a,b) = a + b`.

* `Xthree` is the disjoint union `V/A ⊔ V/B ⊔ V/C` of the three transitive two-element
  `V`-sets;
* `Xreg` is the disjoint union of the regular `V`-set with two fixed points.

Both have six elements and, as we verify, *identical permutation characters*; hence
identical Molien invariants at every subgroup.  Their mark vectors, however, disagree at
the top subgroup (`0` versus `2`), and no rescaling can repair this. -/

/-- The Klein four group, written multiplicatively. -/
abbrev V4 := Multiplicative (ZMod 2 × ZMod 2)

/-- The three index-two characters of the Klein four group. -/
def kleinChar (i : Fin 3) (p : ZMod 2 × ZMod 2) : ZMod 2 := ![p.1, p.2, p.1 + p.2] i

/-- `Xthree = V/A ⊔ V/B ⊔ V/C`: three copies of `ℤ/2`, the `i`-th one acted on through the
character `kleinChar i`. -/
abbrev Xthree := ZMod 2 × Fin 3

instance : SMul V4 Xthree :=
  ⟨fun g x => (x.1 + kleinChar x.2 (Multiplicative.toAdd g), x.2)⟩

instance : MulAction V4 Xthree where
  one_smul := by decide
  mul_smul := by decide

/-- `Xreg = V ⊔ pt ⊔ pt`: the regular `V`-set together with two fixed points. -/
abbrev Xreg := (ZMod 2 × ZMod 2) ⊕ Bool

instance : SMul V4 Xreg :=
  ⟨fun g x => match x with
    | .inl p => .inl (p + Multiplicative.toAdd g)
    | .inr b => .inr b⟩

instance : MulAction V4 Xreg where
  one_smul := by decide
  mul_smul := by decide

instance decMemTopV4 : DecidablePred (· ∈ (⊤ : Subgroup V4)) :=
  fun x => isTrue (Subgroup.mem_top x)

instance decMemBotV4 : DecidablePred (· ∈ (⊥ : Subgroup V4)) :=
  fun x => decidable_of_iff (x = 1) Subgroup.mem_bot.symm












end KleinCounterexample

end D10


