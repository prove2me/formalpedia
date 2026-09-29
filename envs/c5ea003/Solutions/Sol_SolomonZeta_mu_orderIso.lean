-- Prove2me | solution 1 for SolomonZeta.mu_orderIso
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:54:07.276984+00:00
-- url     : https://prove2.me/submissions/9fecf2a9-a088-433f-b1a8-48b14244f889

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
theorem solution{𝕜 : Type*} [AddCommGroup 𝕜] [One 𝕜] {α β : Type*}
    [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
    [PartialOrder β] [LocallyFiniteOrder β] [DecidableEq β] (e : α ≃o β) (a b : α) :
    mu 𝕜 (e a) (e b) = mu 𝕜 a b := by
  have himg : ∀ a b : α, (Finset.Ico a b).image e = Finset.Ico (e a) (e b) := by
    intro a b
    ext y
    simp only [Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.le_iff_le.2 hx.1, e.lt_iff_lt.2 hx.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨e.symm y, ⟨?_, ?_⟩, by simp⟩
      · have h1' : e a ≤ e (e.symm y) := by simpa using h1
        exact e.le_iff_le.1 h1'
      · have h2' : e (e.symm y) < e b := by simpa using h2
        exact e.lt_iff_lt.1 h2'
  have key : ∀ n : ℕ, ∀ a b : α, (Finset.Ico a b).card = n → mu 𝕜 (e a) (e b) = mu 𝕜 a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b hn
      by_cases hab : a = b
      · subst hab; simp
      · rw [mu_apply, mu_apply, if_neg hab, if_neg (fun h => hab (e.injective h))]
        congr 1
        rw [← himg a b, Finset.sum_image (fun x _ y _ h => e.injective h)]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_Ico] at hx
        have hsub : Finset.Ico a x ⊆ Finset.Ico a b := by
          intro z hz
          rw [Finset.mem_Ico] at hz ⊢
          exact ⟨hz.1, lt_of_lt_of_le hz.2 (le_of_lt hx.2)⟩
        have hlt : (Finset.Ico a x).card < (Finset.Ico a b).card :=
          Finset.card_lt_card ⟨hsub, fun hcon => by
            have hmem : x ∈ Finset.Ico a x := hcon (Finset.mem_Ico.2 hx)
            simp at hmem⟩
        exact ih _ (hn ▸ hlt) a x rfl
  exact key _ a b rfl
