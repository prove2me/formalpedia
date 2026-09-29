-- Prove2me | Definitions.Def_Algebra_DerivedFunctors_Resolutions
-- name    : Algebra_DerivedFunctors_Resolutions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:11:00.111105+00:00
-- url     : https://prove2.me/theorems/aa6371d5-ffb6-4f28-a60e-a608e33a8417
-- title:
--   Aether Catalog definitions — Algebra_DerivedFunctors_Resolutions
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.DerivedFunctors.Resolutions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/DerivedFunctors/Resolutions.lean by skeleton subtraction
import Mathlib

/-!
# Concrete projective and injective resolutions

This file constructs two concrete resolutions in the category of `ℤ`-modules
(equivalently, abelian groups):

* `Catalog.DerivedFunctors.zmodShortComplex k`: the short exact sequence
  `0 → ℤ --(·k)--> ℤ --(mod k)--> ZMod k → 0`, which is the standard length-one
  free (hence projective) resolution of the cyclic group `ZMod k` for `k ≠ 0`.

These are used in `Algebra.DerivedFunctors.Ext` to compute `Ext`-groups.
-/

universe u

open CategoryTheory Abelian Limits

namespace Catalog.DerivedFunctors

section ZMod

variable (k : ℕ)

/-- Multiplication by `k` on `ℤ`, as a morphism of `ℤ`-modules. -/
noncomputable def mulZ : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom ((k : ℤ) • LinearMap.id)

/-- Reduction modulo `k`, as a morphism of `ℤ`-modules. -/
noncomputable def redZ : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (ZMod k) :=
  ModuleCat.ofHom (Int.castAddHom (ZMod k)).toIntLinearMap



lemma mulZ_comp_redZ : mulZ k ≫ redZ k = 0 := by
  ext
  show ((((k : ℤ) • (1 : ℤ)) : ℤ) : ZMod k) = 0
  simp

/-- The two-term free resolution `0 → ℤ --(·k)--> ℤ → ZMod k → 0` of `ZMod k`,
packaged as a short complex of `ℤ`-modules. -/
noncomputable def zmodShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk _ _ (mulZ_comp_redZ k)






end ZMod

section Injective

/-- The divisible group `ℚ⧸ℤ`, viewed as a `ℤ`-module. -/
abbrev QmodZ := ℚ ⧸ (AddSubgroup.zmultiples (1 : ℚ))

/-- `ℚ` is a divisible group, hence an injective `ℤ`-module. -/
noncomputable instance : Injective (ModuleCat.of ℤ ℚ) :=
  Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible ℚ).injective)

noncomputable instance : DivisibleBy QmodZ ℤ :=
  haveI : DivisibleBy ℚ ℕ := AddGroup.divisibleByNatOfDivisibleByInt ℚ
  AddGroup.divisibleByIntOfDivisibleByNat QmodZ

/-- `ℚ⧸ℤ` is divisible, hence an injective `ℤ`-module. -/
noncomputable instance : Injective (ModuleCat.of ℤ QmodZ) :=
  Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible QmodZ).injective)

/-- The inclusion `ℤ → ℚ`, as a morphism of `ℤ`-modules. -/
noncomputable def iotaQ : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℚ :=
  ModuleCat.ofHom (Int.castAddHom ℚ).toIntLinearMap

/-- The projection `ℚ → ℚ⧸ℤ`, as a morphism of `ℤ`-modules. -/
noncomputable def projQ : ModuleCat.of ℤ ℚ ⟶ ModuleCat.of ℤ QmodZ :=
  ModuleCat.ofHom (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap

lemma iotaQ_comp_projQ : iotaQ ≫ projQ = 0 := by
  ext
  show (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) ((1 : ℤ) : ℚ) = 0
  simp [QuotientAddGroup.eq_zero_iff]

/-- The two-term injective resolution `0 → ℤ → ℚ → ℚ⧸ℤ → 0` of `ℤ`, packaged as a
short complex of `ℤ`-modules. -/
noncomputable def qShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk _ _ iotaQ_comp_projQ



end Injective

end Catalog.DerivedFunctors


