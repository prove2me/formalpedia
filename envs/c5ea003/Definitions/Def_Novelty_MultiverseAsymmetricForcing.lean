-- Prove2me | Definitions.Def_Novelty_MultiverseAsymmetricForcing
-- name    : Novelty_MultiverseAsymmetricForcing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:49.683622+00:00
-- url     : https://prove2.me/theorems/c234c331-467d-4546-b05a-588a785cf735
-- title:
--   Aether Catalog definitions — Novelty_MultiverseAsymmetricForcing
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MultiverseAsymmetricForcing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MultiverseAsymmetricForcing.lean by skeleton subtraction
import Mathlib
/-
# Asymmetric Forcing — Separating `S4.2` from `S5`

This file **deepens** `MultiverseModalForcing.lean`.  There the concrete forcing
frame was built from single-atom *flips*, which are their own inverse; the
resulting accessibility relation is an equivalence relation, so it validates the
full `S5`.  Real forcing, however, is *asymmetric*: one can pass to a generic
extension but cannot in general force *back* to the ground model.  The modal
logic of forcing is therefore exactly `S4.2`, **not** `S5`.

Here we realise that asymmetry.  Worlds are truth assignments and the
accessibility relation is the pointwise *domination* order

  `dom w v  :=  ∀ a, w a = true → v a = true`

("`v` decides at least as many atoms positively as `w`"): an extension may turn
atoms on but never off.  This relation is

* **reflexive** and **transitive** (`dom_refl`, `dom_trans`) — so it validates
  `T` and `4`;
* **confluent** (`dom_confluent`), the common upper bound being the pointwise
  `or` (join) — so it validates the characteristic forcing axiom `.2`
  (`asym_dot2`);
* but **not symmetric / not Euclidean**, and crucially it **refutes axiom `5`**
  (`asym_refutes_five`): from the bottom world `◇P` can hold while `□◇P` fails.

Thus the asymmetric forcing frame validates `S4.2` yet falsifies `S5`, giving a
clean semantic separation of the two logics — the phenomenon that makes the
modal logic of forcing genuinely `S4.2`.

Everything is proved over `Mathlib` and the file is self-contained.
-/

namespace MultiverseAsymmetricForcing

open Relation

/-! ## Abstract Kripke layer (self-contained) -/

section Kripke

variable {W : Type*}

/-- Necessity: `Box R P w` holds when `P` holds in every `R`-successor of `w`. -/
def Box (R : W → W → Prop) (P : W → Prop) (w : W) : Prop := ∀ v, R w v → P v

/-- Possibility: `Dia R P w` holds when `P` holds in some `R`-successor of `w`. -/
def Dia (R : W → W → Prop) (P : W → Prop) (w : W) : Prop := ∃ v, R w v ∧ P v

variable {R : W → W → Prop} {P Q : W → Prop} {w : W}





/-- A relation is **confluent** (directed) when any two successors of a point have
    a common successor. -/
def Confluent (R : W → W → Prop) : Prop :=
  ∀ x y z, R x y → R x z → ∃ u, R y u ∧ R z u

/-- A relation is **Euclidean** when successors of a point are related. -/
def EuclideanRel (R : W → W → Prop) : Prop :=
  ∀ x y z, R x y → R x z → R y z




end Kripke

/-! ## The asymmetric (domination) forcing frame -/

section Asymmetric

variable {α : Type*}

/-- A `World` is a truth assignment to atomic set-theoretic assertions. -/
abbrev World (α : Type*) := α → Bool

/-- **Asymmetric accessibility**: `dom w v` means `v` decides at least as many
    atoms positively as `w`.  An extension may switch atoms on, never off. -/
def dom (w v : World α) : Prop := ∀ a, w a = true → v a = true




/-! ### The asymmetric frame validates `S4.2` -/




end Asymmetric

/-! ## Separation: asymmetric forcing refutes `5`

We witness the failure of `S5` in the two-atom model `World Bool`.  From the
bottom world `bot` (all atoms false) the predicate "`= m`" (the world in which
exactly the atom `true` holds) is *possible*, yet not *necessarily possible*:
the world `top` (all atoms true) is accessible from `bot` but cannot reach `m`,
since reaching `m` would require switching the atom `false` back off. -/

section Separation

/-- The bottom world: every atom false. -/
def bot : World Bool := fun _ => false

/-- The world in which exactly the atom `true` holds. -/
def m : World Bool := fun a => a

/-- The world in which every atom is true. -/
def top : World Bool := fun _ => true







end Separation

end MultiverseAsymmetricForcing


