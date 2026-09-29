-- Prove2me | solution 1 for SolomonZeta.card_hom_prod_submodule
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:54:06.741725+00:00
-- url     : https://prove2.me/submissions/f5877210-1378-41a1-a10b-36cc103b3b14

-- Sol generated from Shared/SolomonZeta/Multiplicativity.lean
import Mathlib
import Definitions.Def_Shared_SolomonZeta_Core
import Definitions.Def_Shared_SolomonZeta_Multiplicativity
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

open SolomonZeta

open Finset IncidenceAlgebra


/-! ### Möbius functions are invariant under order isomorphisms -/


/-! ### Coprime splitting of submodule lattices -/

variable {R M X₁ X₂ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]





/-! ### Multiplicativity of the Möbius weight -/






open SolomonZeta in
theorem solution(Y₁ : Submodule R X₁) (Y₂ : Submodule R X₂) :
    Nat.card (M →ₗ[R] (Y₁.prod Y₂)) = Nat.card (M →ₗ[R] Y₁) * Nat.card (M →ₗ[R] Y₂) := by
  have esub : ↥(Y₁.prod Y₂) ≃ₗ[R] (↥Y₁ × ↥Y₂) :=
    { toFun := fun z => (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2, p.2.2⟩⟩
      left_inv := fun z => by ext <;> rfl
      right_inv := fun p => by ext <;> rfl }
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.trans ?_ (LinearMap.prodEquiv (R := R) (S := ℕ)
      (M := M) (M₂ := ↥Y₁) (M₃ := ↥Y₂)).toEquiv.symm)
  exact ⟨fun f => esub.toLinearMap ∘ₗ f, fun g => esub.symm.toLinearMap ∘ₗ g,
    fun f => LinearMap.ext fun m => by simp, fun g => LinearMap.ext fun m => by simp⟩
