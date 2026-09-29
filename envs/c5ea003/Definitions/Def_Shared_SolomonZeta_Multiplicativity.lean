-- Prove2me | Definitions.Def_Shared_SolomonZeta_Multiplicativity
-- name    : Shared_SolomonZeta_Multiplicativity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:14:22.424414+00:00
-- url     : https://prove2.me/theorems/91cf0ddb-3946-4478-94cb-eddbd1b82c12
-- title:
--   Aether Catalog definitions — Shared_SolomonZeta_Multiplicativity
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.SolomonZeta.Multiplicativity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/SolomonZeta/Multiplicativity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_SolomonZeta_Core
/-
# Euler factorization of the refined Solomon zeta coefficients

The Solomon zeta function of a lattice factors into local Euler factors.  On the level of the
*refined* (Bushnell–Reiner style) coefficients — which record the isomorphism type `X` of the
quotient rather than just its cardinality — this factorization takes the form of a
multiplicativity statement:

  if the finite modules `X₁` and `X₂` are annihilated by coprime integers `a` and `b`, then
  the Möbius weight of `X₁ × X₂` is the product of the Möbius weights of `X₁` and `X₂`,
  and consequently the refined zeta coefficients multiply.

The proof is structural and proceeds in three steps:

1. `SolomonZeta.mu_orderIso` — the Möbius function of a locally finite poset is invariant under
   order isomorphisms (proved by strong induction on the size of the interval);
2. `SolomonZeta.submodule_prod_split` — under coprimality every submodule of `X₁ × X₂` is a
   product of submodules, giving an order isomorphism of submodule lattices
   `SolomonZeta.coprimeSubmoduleOrderIso`;
3. Mathlib's `IncidenceAlgebra.mu_prod_mu` then evaluates the Möbius function of the product
   poset, and the Hom-counts factor because `Hom(M, Y₁ × Y₂) = Hom(M, Y₁) × Hom(M, Y₂)`.
-/

namespace SolomonZeta

open Finset IncidenceAlgebra

noncomputable instance instDecLESubmodule {R X : Type*} [Ring R] [AddCommGroup X] [Module R X] :
    DecidableLE (Submodule R X) := Classical.decRel _

/-! ### Möbius functions are invariant under order isomorphisms -/


/-! ### Coprime splitting of submodule lattices -/

variable {R M X₁ X₂ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]

/-- If `X₁` and `X₂` are annihilated by coprime integers, every submodule of `X₁ × X₂` is a
product of submodules. -/
theorem submodule_prod_split (a b : ℕ) (hab : Nat.Coprime a b)
    (h1 : ∀ x : X₁, (a : ℤ) • x = 0) (h2 : ∀ y : X₂, (b : ℤ) • y = 0)
    (Y : Submodule R (X₁ × X₂)) :
    Y = (Y.map (LinearMap.fst R X₁ X₂)).prod (Y.map (LinearMap.snd R X₁ X₂)) := by
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * a + v * b = 1 := by
    have hco : IsCoprime (a : ℤ) (b : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by simpa using hab)
    obtain ⟨u, v, h⟩ := hco
    exact ⟨u, v, h⟩
  apply le_antisymm
  · intro z hz
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
  · rintro ⟨x, y⟩ ⟨⟨z, hz, hx⟩, ⟨w, hw, hy⟩⟩
    simp only [LinearMap.fst_apply, LinearMap.snd_apply] at hx hy
    have hxz : ((x : X₁), (0 : X₂)) ∈ Y := by
      have hmem : (v * b : ℤ) • z ∈ Y := Submodule.smul_of_tower_mem Y _ hz
      have hz2 : (v * b : ℤ) • z = (x, 0) := by
        rw [← hx]
        ext
        · show (v * b : ℤ) • z.1 = z.1
          have hzero : ((u * a) : ℤ) • z.1 = 0 := by rw [mul_smul, h1 z.1, smul_zero]
          have h3 : ((u * a + v * b) : ℤ) • z.1 = z.1 := by rw [huv, one_smul]
          rw [add_smul, hzero, zero_add] at h3
          exact h3
        · show (v * b : ℤ) • z.2 = 0
          rw [mul_smul, h2 z.2, smul_zero]
      rwa [hz2] at hmem
    have hyw : ((0 : X₁), (y : X₂)) ∈ Y := by
      have hmem : (u * a : ℤ) • w ∈ Y := Submodule.smul_of_tower_mem Y _ hw
      have hw2 : (u * a : ℤ) • w = (0, y) := by
        rw [← hy]
        ext
        · show (u * a : ℤ) • w.1 = 0
          rw [mul_smul, h1 w.1, smul_zero]
        · show (u * a : ℤ) • w.2 = w.2
          have hzero : ((v * b) : ℤ) • w.2 = 0 := by rw [mul_smul, h2 w.2, smul_zero]
          have h3 : ((u * a + v * b) : ℤ) • w.2 = w.2 := by rw [huv, one_smul]
          rw [add_smul, hzero, add_zero] at h3
          exact h3
      rwa [hw2] at hmem
    simpa using Y.add_mem hxz hyw

theorem map_fst_prod (Y₁ : Submodule R X₁) (Y₂ : Submodule R X₂) :
    (Y₁.prod Y₂).map (LinearMap.fst R X₁ X₂) = Y₁ := by
  ext x
  simp only [Submodule.mem_map, LinearMap.fst_apply, Submodule.mem_prod]
  exact ⟨by rintro ⟨z, ⟨hz1, -⟩, rfl⟩; exact hz1,
    fun hx => ⟨(x, 0), ⟨hx, Y₂.zero_mem⟩, rfl⟩⟩

theorem map_snd_prod (Y₁ : Submodule R X₁) (Y₂ : Submodule R X₂) :
    (Y₁.prod Y₂).map (LinearMap.snd R X₁ X₂) = Y₂ := by
  ext y
  simp only [Submodule.mem_map, LinearMap.snd_apply, Submodule.mem_prod]
  exact ⟨by rintro ⟨z, ⟨-, hz2⟩, rfl⟩; exact hz2,
    fun hy => ⟨(0, y), ⟨Y₁.zero_mem, hy⟩, rfl⟩⟩

/-- **The submodule lattice of a coprime product splits.** -/
def coprimeSubmoduleOrderIso (a b : ℕ) (hab : Nat.Coprime a b)
    (h1 : ∀ x : X₁, (a : ℤ) • x = 0) (h2 : ∀ y : X₂, (b : ℤ) • y = 0) :
    Submodule R (X₁ × X₂) ≃o Submodule R X₁ × Submodule R X₂ where
  toFun := fun Y => (Y.map (LinearMap.fst R X₁ X₂), Y.map (LinearMap.snd R X₁ X₂))
  invFun := fun p => p.1.prod p.2
  left_inv := fun Y => (submodule_prod_split a b hab h1 h2 Y).symm
  right_inv := fun p => by
    ext1
    · exact map_fst_prod p.1 p.2
    · exact map_snd_prod p.1 p.2
  map_rel_iff' := by
    intro Y Z
    constructor
    · rintro ⟨hle1, hle2⟩
      rw [submodule_prod_split a b hab h1 h2 Y, submodule_prod_split a b hab h1 h2 Z]
      exact Submodule.prod_mono hle1 hle2
    · intro hle
      exact ⟨Submodule.map_mono hle, Submodule.map_mono hle⟩

/-! ### Multiplicativity of the Möbius weight -/





end SolomonZeta


