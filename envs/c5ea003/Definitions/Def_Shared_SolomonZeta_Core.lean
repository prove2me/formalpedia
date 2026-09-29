-- Prove2me | Definitions.Def_Shared_SolomonZeta_Core
-- name    : Shared_SolomonZeta_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:36:15.519506+00:00
-- url     : https://prove2.me/theorems/ac8bb81c-26b6-4362-b4d6-0a14d4f53fb2
-- title:
--   Aether Catalog definitions — Shared_SolomonZeta_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.SolomonZeta.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/SolomonZeta/Core.lean by skeleton subtraction
import Mathlib
/-
# The Möbius engine behind Solomon's zeta functions

This file formalizes the module-theoretic counting engine underlying the effective
form of Solomon's first conjecture for zeta functions of lattices over orders
(cf. the ArXiv paper *Solomon zeta functions over arithmetic orders*).

The Solomon zeta function of a lattice `M` over an order is the Dirichlet series
`ζ_M(s) = Σ_{N ≤ M of finite index} [M : N]^{-s}`.  Its coefficients are obtained by
grouping the finite-index submodules `N` according to the isomorphism class of the
finite quotient `M / N`.  The key *effective* input is the identity

  `#Aut(X) · #{N ≤ M : M/N ≅ X}  =  Σ_{Y ≤ X} μ(Y, X) · #Hom(M, Y)`,

where `μ` is the Möbius function of the (finite) lattice of submodules of `X`.
The right-hand side is exactly the "polynomial defined using the Möbius function of
finite submodule posets" that weights each term in the effective formula: for `M`
a free module of rank `n` it is literally the integer polynomial
`Σ_{Y ≤ X} μ(Y, X) · |Y|^n` evaluated on the submodule poset of `X`.

Main results:
* `SolomonZeta.homLeCount_eq_sum_homEqCount` — partition of `Hom(M, Y)` by image;
* `SolomonZeta.homEqCount_top_eq_autCard_mul_quotIsoCount` — orbit theorem
  (`Aut X` acts freely on surjections with orbits the kernels);
* `SolomonZeta.autCard_mul_quotIsoCount_eq_mobiusWeight` — the effective formula.
-/

namespace SolomonZeta

open Finset IncidenceAlgebra

/-! ### Finiteness and order instances on submodule lattices -/

/-- The lattice of submodules of a finite module is a finite type. -/
noncomputable instance instFintypeSubmodule {R X : Type*} [Ring R] [AddCommGroup X] [Module R X]
    [Finite X] : Fintype (Submodule R X) := Fintype.ofFinite _

noncomputable instance instDecEqSubmodule {R X : Type*} [Ring R] [AddCommGroup X] [Module R X] :
    DecidableEq (Submodule R X) := Classical.decEq _

open Classical in
/-- A finite submodule lattice is locally finite, so its Möbius function is defined. -/
noncomputable instance instLFOSubmodule {R X : Type*} [Ring R] [AddCommGroup X] [Module R X]
    [Finite X] : LocallyFiniteOrder (Submodule R X) := Fintype.toLocallyFiniteOrder

variable {R M X : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup X] [Module R X]

/-- Hom-sets from a finitely generated module into a finite module are finite. -/
instance finite_linearMap [Module.Finite R M] [Finite X] : Finite (M →ₗ[R] X) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  have hinj : Function.Injective (fun (f : M →ₗ[R] X) => fun (x : ↥(s : Set M)) => f x) := by
    intro f g h
    apply LinearMap.ext_on hs
    intro x hx
    exact congrFun h ⟨x, hx⟩
  haveI : Finite ↥(s : Set M) := s.finite_toSet
  exact Finite.of_injective _ hinj

/-! ### The counting functions -/

variable (R M X)

/-- The number of `R`-linear maps `M → X` whose image is contained in `Y`. -/
noncomputable def homLeCount (Y : Submodule R X) : ℕ :=
  Nat.card {f : M →ₗ[R] X // LinearMap.range f ≤ Y}

/-- The number of `R`-linear maps `M → X` whose image is exactly `Y`. -/
noncomputable def homEqCount (Y : Submodule R X) : ℕ :=
  Nat.card {f : M →ₗ[R] X // LinearMap.range f = Y}

/-- The number of submodules `N ≤ M` with `M / N ≅ X`: the `X`-part of the Solomon
zeta coefficient of the lattice `M`. -/
noncomputable def quotIsoCount : ℕ := Nat.card {N : Submodule R M // Nonempty ((M ⧸ N) ≃ₗ[R] X)}

/-- The order of the automorphism group of `X`. -/
noncomputable def autCard : ℕ := Nat.card (X ≃ₗ[R] X)

/-- The Möbius weight of the pair `(M, X)`: the value at `M` of the integral polynomial
`Σ_{Y ≤ X} μ(Y, X) · T(Y)` on the submodule poset of `X`, with `T(Y) = #Hom(M, Y)`. -/
noncomputable def mobiusWeight [Finite X] : ℤ :=
  ∑ Y ∈ Finset.Iic (⊤ : Submodule R X), mu ℤ Y ⊤ * (Nat.card (M →ₗ[R] Y) : ℤ)

variable {R M X}

/-! ### Step 1: partition of the Hom-set by image -/

/-- Maps into `X` with image inside `Y` are the same thing as maps into `Y`. -/
noncomputable def homLeEquiv (Y : Submodule R X) :
    {f : M →ₗ[R] X // LinearMap.range f ≤ Y} ≃ (M →ₗ[R] Y) where
  toFun := fun f => f.1.codRestrict Y (fun x => f.2 ⟨x, rfl⟩)
  invFun := fun g => ⟨Y.subtype ∘ₗ g, by rintro x ⟨m, rfl⟩; exact (g m).2⟩
  left_inv := by intro f; ext m; rfl
  right_inv := by intro g; ext m; rfl

theorem homLeCount_eq_card_hom (Y : Submodule R X) :
    homLeCount R M X Y = Nat.card (M →ₗ[R] Y) :=
  Nat.card_congr (homLeEquiv Y)

/-- Grouping linear maps by their image: `#Hom(M, Y) = Σ_{Z ≤ Y} #{f : im f = Z}`. -/
theorem homLeCount_eq_sum_homEqCount [Finite X] [Module.Finite R M] (Y : Submodule R X) :
    homLeCount R M X Y = ∑ Z ∈ Finset.Iic Y, homEqCount R M X Z := by
  classical
  haveI : Fintype (M →ₗ[R] X) := Fintype.ofFinite _
  rw [homLeCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f : M →ₗ[R] X => LinearMap.range f)
      (t := Finset.Iic Y) (by intro f hf; simp at hf ⊢; exact hf)]
  refine Finset.sum_congr rfl ?_
  intro Z hZ
  simp only [Finset.mem_Iic] at hZ
  rw [homEqCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hZ, h⟩⟩

/-! ### Step 2: Möbius inversion on the submodule poset -/

/-- Möbius inversion over the finite poset of submodules of `X`: the number of
*surjections* `M ↠ X` is the Möbius-weighted alternating sum of the Hom-counts. -/
theorem homEqCount_top_eq_mobiusWeight [Finite X] [Module.Finite R M] :
    (homEqCount R M X ⊤ : ℤ) = mobiusWeight R M X := by
  classical
  have key := IncidenceAlgebra.moebius_inversion_bot
    (𝕜 := ℤ) (α := Submodule R X)
    (fun Z => (homEqCount R M X Z : ℤ)) (fun Y => (homLeCount R M X Y : ℤ))
    (by
      intro Y
      show (homLeCount R M X Y : ℤ) = ∑ Z ∈ Finset.Iic Y, (homEqCount R M X Z : ℤ)
      rw [homLeCount_eq_sum_homEqCount Y]
      push_cast
      rfl) ⊤
  rw [key, mobiusWeight]
  exact Finset.sum_congr rfl fun Y _ => by rw [homLeCount_eq_card_hom]

/-! ### Step 3: the orbit theorem -/

/-- Surjections `M ↠ X` with kernel `N` correspond to isomorphisms `M / N ≅ X`. -/
noncomputable def fiberEquiv (N : Submodule R M) :
    {f : M →ₗ[R] X // LinearMap.range f = ⊤ ∧ LinearMap.ker f = N} ≃ ((M ⧸ N) ≃ₗ[R] X) where
  toFun := fun f => LinearEquiv.ofBijective (N.liftQ f.1 (le_of_eq f.2.2.symm))
      ⟨by
        rw [← LinearMap.ker_eq_bot]
        exact Submodule.ker_liftQ_eq_bot' N f.1 f.2.2.symm,
       by
        rw [← LinearMap.range_eq_top, Submodule.range_liftQ]
        exact f.2.1⟩
  invFun := fun e => ⟨e.toLinearMap ∘ₗ N.mkQ, by
      rw [LinearMap.range_eq_top]
      exact e.surjective.comp N.mkQ_surjective, by
      ext m
      simp⟩
  left_inv := by intro f; ext m; rfl
  right_inv := by
    intro e
    ext m
    induction m using Quotient.inductionOn with
    | h m => rfl

/-- The set of isomorphisms `M / N ≅ X` is a torsor under `Aut X`. -/
def autTorsorEquiv {N : Submodule R M} (e₀ : (M ⧸ N) ≃ₗ[R] X) :
    ((M ⧸ N) ≃ₗ[R] X) ≃ (X ≃ₗ[R] X) where
  toFun := fun e => e₀.symm.trans e
  invFun := fun a => e₀.trans a
  left_inv := by intro e; ext m; simp
  right_inv := by intro a; ext x; simp

/-- **Orbit theorem.** The number of surjections `M ↠ X` equals `#Aut(X)` times the number
of submodules `N ≤ M` with `M / N ≅ X`. -/
theorem homEqCount_top_eq_autCard_mul_quotIsoCount [Finite X] [Module.Finite R M] :
    homEqCount R M X ⊤ = autCard R X * quotIsoCount R M X := by
  classical
  haveI : Fintype (M →ₗ[R] X) := Fintype.ofFinite _
  set s : Finset (M →ₗ[R] X) := Finset.univ.filter (fun f => LinearMap.range f = ⊤) with hs
  set T : Finset (Submodule R M) := s.image (fun f => LinearMap.ker f) with hT
  have hTmem : ∀ N : Submodule R M, N ∈ T ↔ Nonempty ((M ⧸ N) ≃ₗ[R] X) := by
    intro N
    rw [hT, Finset.mem_image]
    constructor
    · rintro ⟨f, hf, rfl⟩
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact ⟨fiberEquiv (LinearMap.ker f) ⟨f, hf, rfl⟩⟩
    · rintro ⟨e⟩
      refine ⟨((fiberEquiv N).symm e).1, ?_, ((fiberEquiv N).symm e).2.2⟩
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ((fiberEquiv N).symm e).2.1
  have h1 : homEqCount R M X ⊤ = s.card := by
    rw [homEqCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 : s.card = ∑ N ∈ T, (s.filter (fun f => LinearMap.ker f = N)).card :=
    Finset.card_eq_sum_card_image _ _
  have h3 : ∀ N ∈ T, (s.filter (fun f => LinearMap.ker f = N)).card = autCard R X := by
    intro N hN
    obtain ⟨e₀⟩ := (hTmem N).1 hN
    have hcard : (s.filter (fun f => LinearMap.ker f = N)).card
        = Fintype.card {f : M →ₗ[R] X // LinearMap.range f = ⊤ ∧ LinearMap.ker f = N} := by
      rw [Fintype.card_subtype, hs, Finset.filter_filter]
    rw [hcard, ← Nat.card_eq_fintype_card, autCard]
    exact Nat.card_congr ((fiberEquiv N).trans (autTorsorEquiv e₀))
  have h4 : quotIsoCount R M X = T.card := by
    have hset : {N : Submodule R M | Nonempty ((M ⧸ N) ≃ₗ[R] X)} = (T : Set (Submodule R M)) := by
      ext N; simpa using (hTmem N).symm
    rw [quotIsoCount, show {N : Submodule R M // Nonempty ((M ⧸ N) ≃ₗ[R] X)}
      = ↥({N : Submodule R M | Nonempty ((M ⧸ N) ≃ₗ[R] X)}) from rfl, hset]
    simp
  rw [h1, h2, Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, h4, mul_comm]

/-! ### The effective formula -/

/-- **Effective Solomon coefficient formula.**  For a finitely generated module `M` over a
ring `R` and a finite `R`-module `X`, the number of submodules `N ≤ M` with `M / N ≅ X`,
weighted by `#Aut(X)`, is given by the Möbius-weighted alternating sum of Hom-counts over
the submodule poset of `X`. -/
theorem autCard_mul_quotIsoCount_eq_mobiusWeight [Finite X] [Module.Finite R M] :
    (autCard R X : ℤ) * (quotIsoCount R M X : ℤ) = mobiusWeight R M X := by
  rw [← homEqCount_top_eq_mobiusWeight]
  exact_mod_cast homEqCount_top_eq_autCard_mul_quotIsoCount.symm

end SolomonZeta


