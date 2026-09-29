-- Prove2me | solution 1 for Catalog.DerivedFunctors.ext_fg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:04:56.623677+00:00
-- url     : https://prove2.me/submissions/da0103db-e914-412e-bcdb-1bfaa4cb1120

-- Sol generated from Algebra/DerivedFunctors/ExtFinitelyGenerated.lean
import Mathlib
import Definitions.Def_Algebra_DerivedFunctors_ExtFinitelyGenerated
import Definitions.Def_Algebra_DerivedFunctors_Resolutions

/-!
# Projective dimension at most one for finitely generated abelian groups

Every finitely generated `ℤ`-module `X` admits a free presentation `0 → K → ℤⁿ → X → 0`, and the
kernel `K`, being a submodule of a finitely generated free module over a PID, is again free.
Hence `X` has projective dimension at most one and all higher `Ext`-groups out of `X` vanish.

This generalises `Catalog.DerivedFunctors.ext_zmod_eq_zero` (the case `X = ℤ/k`).

Main results:

* `Catalog.DerivedFunctors.ext_eq_zero_of_projective_presentation`: if `X` sits in a short exact
  sequence `0 → P₁ → P₀ → X → 0` with `P₁`, `P₀` projective, then `Extⁿ⁺²(X, Y) = 0`;
* `Catalog.DerivedFunctors.free_ker_of_fin`: the kernel of a linear map `ℤⁿ → X` is a free
  `ℤ`-module;
* `Catalog.DerivedFunctors.kerShortComplex_shortExact`: the presentation `0 → ker f → M → X → 0`
  attached to a surjection `f` is short exact;
* `Catalog.DerivedFunctors.ext_fg_eq_zero`: **`Extⁿ⁺²(X, Y) = 0` for every finitely generated
  `ℤ`-module `X` and every `ℤ`-module `Y`**.
-/

open CategoryTheory Abelian Limits

open Catalog.DerivedFunctors

/-- **Projective dimension at most one gives vanishing of higher `Ext`.**  If `X = S.X₃` sits in a
short exact sequence `0 → S.X₁ → S.X₂ → X → 0` with `S.X₁` and `S.X₂` projective, then all
`Ext`-groups out of `X` in degrees `≥ 2` vanish. -/
theorem ext_eq_zero_of_projective_presentation (S : ShortComplex (ModuleCat.{0} ℤ))
    (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂] (Y : ModuleCat.{0} ℤ) (n : ℕ)
    (x : Ext S.X₃ Y (n + 2)) : x = 0 := by
  obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃ (S := S) hS Y x
    (Ext.eq_zero_of_projective _) (n₀ := n + 1) (by omega)
  rw [← hx₁, show x₁ = 0 from Ext.eq_zero_of_projective x₁]
  simp

/-- The kernel of a linear map out of `ℤⁿ` is a free `ℤ`-module: it is a submodule of a finitely
generated free module over the PID `ℤ`. -/
theorem free_ker_of_fin {n : ℕ} {X : Type} [AddCommGroup X]
    (f : (Fin n → ℤ) →ₗ[ℤ] X) : Module.Free ℤ (LinearMap.ker f) := by
  obtain ⟨m, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ (Fin n)) (LinearMap.ker f)
  exact Module.Free.of_basis b





/-- For a surjective `f` the presentation complex is short exact. -/
theorem kerShortComplex_shortExact {M X : Type} [AddCommGroup M] [AddCommGroup X]
    (f : M →ₗ[ℤ] X) (hf : Function.Surjective f) :
    (kerShortComplex f).ShortExact := by
  haveI : Mono (kerShortComplex f).f :=
    (ModuleCat.mono_iff_injective _).2 Subtype.coe_injective
  haveI : Epi (kerShortComplex f).g := (ModuleCat.epi_iff_surjective _).2 hf
  refine { exact := ?_ }
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩



open Catalog.DerivedFunctors in
theorem solution(X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Y : ModuleCat.{0} ℤ) (n : ℕ) (x : Ext (ModuleCat.of ℤ X) Y (n + 2)) : x = 0 := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := X)
  set f : (Fin m → ℤ) →ₗ[ℤ] X := Fintype.linearCombination ℤ s with hf
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, hf, Fintype.range_linearCombination, hs]
  haveI : Module.Free ℤ (LinearMap.ker f) := free_ker_of_fin f
  haveI : Projective (kerShortComplex f).X₁ :=
    inferInstanceAs (Projective (ModuleCat.of ℤ (LinearMap.ker f)))
  haveI : Projective (kerShortComplex f).X₂ :=
    inferInstanceAs (Projective (ModuleCat.of ℤ (Fin m → ℤ)))
  exact ext_eq_zero_of_projective_presentation (kerShortComplex f)
    (kerShortComplex_shortExact f hsurj) Y n x
