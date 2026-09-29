-- Prove2me | Definitions.Def_Applications_CategoricalPhysics_CobordismShadow
-- name    : Applications_CategoricalPhysics_CobordismShadow
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:01.345919+00:00
-- url     : https://prove2.me/theorems/020f6072-b150-430a-8b9f-d9d75c12dc8d
-- title:
--   Aether Catalog definitions — Applications_CategoricalPhysics_CobordismShadow
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CategoricalPhysics.CobordismShadow`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CategoricalPhysics/CobordismShadow.lean by skeleton subtraction
import Mathlib

/-!
# A rigorous algebraic shadow of the cobordism hypothesis

The literal claim that *every* physical theory must be an `(∞,2)`-category is not a
mathematical proposition until “physical theory” and “must” are specified.  This file
therefore isolates a precise, falsifiable core: a freely generated dualizable sector has
an integer-valued charge group, and every additive shadow out of it is uniquely fixed by
its values on generators.  This is the decategorified universal-property pattern of the
cobordism hypothesis.

The last results separate two often conflated questions about computability.  Evaluation
is an explicit finite sum once generator data are available, but unrestricted generator
data can encode an arbitrary predicate.  Thus universality alone implies neither
computability nor noncomputability.
-/

namespace CategoricalPhysics

/-- The decategorified object group of a freely generated dualizable theory.
`Finsupp` enforces that each expression uses only finitely many generators, while
integer coefficients model tensor powers and formal duals. -/
abbrev DualCharge (G : Type*) := G →₀ ℤ

/-- The positively generated, non-dual fragment. -/
abbrev PositiveCharge (G : Type*) := G →₀ ℕ

/-- A decategorified additive shadow of a dualizable theory. -/
abbrev AdditiveShadow (G A : Type*) [AddCommGroup A] := DualCharge G →+ A

/-- The value assigned to an individual fully dualizable generator. -/
noncomputable def generatorValue {G A : Type*} [AddCommGroup A]
    (Z : AdditiveShadow G A) (g : G) : A := Z (Finsupp.single g 1)

/-- Explicit extension of generator data to all finite formal tensor/dual expressions. -/
noncomputable def extendShadow {G A : Type*} [AddCommGroup A]
    (v : G → A) : AdditiveShadow G A :=
  Finsupp.liftAddHom (fun g =>
    { toFun := fun n : ℤ => n • v g
      map_zero' := zero_zsmul (v g)
      map_add' := fun m n => add_zsmul (v g) m n })

/-
**Universal property (existence).** Any assignment on generators extends to a
shadow, including negative coefficients corresponding to duals.
-/

/-
**Universal property (uniqueness).** A shadow is completely determined by its
values on the fully dualizable generators.
-/

/-
The promised universal property, phrased as unique existence.
-/

/-
Three named sectors (for example, decategorified TQFT, CFT, and string
sectors) can be bundled into one universal shadow. Each component is retained in the
product rather than being identified without justification.
-/

/-
Duality is visible in every additive shadow as negation.
-/

/-
Tensor composition is visible in every additive shadow as addition.
-/



/-
The generator in the positive theory has no additive inverse.  This is a formal
counterexample to the bare algebraic assertion that every tensor theory already has
all duals; additional physical/categorical hypotheses are indispensable.
-/

/-
Evaluation of the universal extension is a finite sum.  This equation is the
computational content: no search over an infinite category is involved.
-/

/-- An unrestricted bit assignment gives an additive shadow on positive charges. -/
noncomputable def bitOracleShadow (p : ℕ → Bool) : PositiveCharge ℕ →+ ZMod 2 :=
  Finsupp.liftAddHom (fun n =>
    { toFun := fun k : ℕ => k • (if p n then 1 else 0)
      map_zero' := zero_nsmul _
      map_add' := fun a b => add_nsmul _ a b })

/-
Every bit of the supplied assignment can be recovered by probing a singleton.
Consequently the universal construction can carry arbitrary oracle information when
its generator assignment is itself unrestricted.
-/

/-
Two oracle assignments induce the same shadow exactly when they are the same.
This strengthens recoverability to an embedding result.
-/

end CategoricalPhysics


