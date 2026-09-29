-- Prove2me | solution 1 for SolomonZeta.mobiusWeight_prod_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:55:55.232974+00:00
-- url     : https://prove2.me/submissions/3afee684-030c-4a92-8961-89e0318b06fe

-- Sol generated from Shared/SolomonZeta/Multiplicativity.lean
import Mathlib
import Definitions.Def_Shared_SolomonZeta_Core
import Definitions.Def_Shared_SolomonZeta_Multiplicativity
import Theorems.Thm_SolomonZeta_card_hom_prod_submodule
import Theorems.Thm_SolomonZeta_mu_orderIso
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


theorem mobiusWeight_eq_sum_univ [Finite X₁] :
    mobiusWeight R M X₁
      = ∑ Y : Submodule R X₁, mu ℤ Y ⊤ * (Nat.card (M →ₗ[R] Y) : ℤ) := by
  rw [mobiusWeight]
  congr 1
  ext Y
  simp




open SolomonZeta in
theorem solution[Finite X₁] [Finite X₂] (a b : ℕ) (hab : Nat.Coprime a b)
    (h1 : ∀ x : X₁, (a : ℤ) • x = 0) (h2 : ∀ y : X₂, (b : ℤ) • y = 0) :
    mobiusWeight R M (X₁ × X₂) = mobiusWeight R M X₁ * mobiusWeight R M X₂ := by
  classical
  set e := coprimeSubmoduleOrderIso (R := R) a b hab h1 h2 with he
  have htop : e ⊤ = (⊤, ⊤) := by
    have h1' : (⊤ : Submodule R (X₁ × X₂)).map (LinearMap.fst R X₁ X₂) = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top]
      exact Prod.fst_surjective
    have h2' : (⊤ : Submodule R (X₁ × X₂)).map (LinearMap.snd R X₁ X₂) = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top]
      exact Prod.snd_surjective
    exact Prod.ext h1' h2'
  rw [mobiusWeight_eq_sum_univ, mobiusWeight_eq_sum_univ, mobiusWeight_eq_sum_univ]
  rw [← Equiv.sum_comp e.symm.toEquiv
    (fun Y : Submodule R (X₁ × X₂) => mu ℤ Y ⊤ * (Nat.card (M →ₗ[R] Y) : ℤ))]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun Y₁ _ => Finset.sum_congr rfl fun Y₂ _ => ?_
  have hsymm : e.symm.toEquiv (Y₁, Y₂) = Y₁.prod Y₂ := rfl
  have hmu : mu ℤ (e.symm.toEquiv (Y₁, Y₂)) ⊤ = mu ℤ Y₁ ⊤ * mu ℤ Y₂ ⊤ := by
    show mu ℤ (e.symm (Y₁, Y₂)) ⊤ = mu ℤ Y₁ ⊤ * mu ℤ Y₂ ⊤
    have := mu_orderIso (𝕜 := ℤ) e (e.symm (Y₁, Y₂)) ⊤
    rw [e.apply_symm_apply, htop] at this
    rw [← this, ← IncidenceAlgebra.mu_prod_mu (𝕜 := ℤ)
      (α := Submodule R X₁) (β := Submodule R X₂)]
    rfl
  rw [hmu, hsymm, card_hom_prod_submodule]
  push_cast
  ring
