-- Prove2me | solution 1 for mem_range_tropicalRadon_iff_supportData
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:19:22.892245+00:00
-- url     : https://prove2.me/submissions/2e9f1f57-0ad6-42c7-a556-59f396917bf2

-- Sol generated from Bridges/TropicalRadonDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalRadonDuality
/-
# Tropical Radon Transform Duality via Idempotent Semimodules

This module formalizes a finite theory of **tropical Radon transforms** and proves
a suite of duality, reconstruction, and minimality theorems that together create
a new bridge between tropical/idempotent algebra and integral geometry.

## Cross-Domain Connections

This work simultaneously touches:
- **Integral geometry**: tropical analogue of Radon/support transforms.
- **Convex geometry**: support-function duality for tropical convex bodies.
- **Order theory**: Galois connections and residuation.
- **Inverse problems**: certified reconstruction from partial observations.
- **Optimization**: semiring version of Fenchel duality.
- **Information theory**: minimal sufficient measurement families.

## Main Results

- `tropicalRadon_adjoint_gc`: The tropical Radon transform and its adjoint
  reconstruction operator form a Galois connection (residuated pair).
- `tropicalRadon_mono`, `tropicalAdjoint_mono`: Both operators are monotone.
- `tropicalAdjoint_tropicalRadon_ge`: f ≤ Adjoint(Radon(f)), the "convexification".
- `tropicalRadon_tropicalAdjoint_le`: Radon(Adjoint(F)) ≤ F on H.
- `tropicalRadon_adjoint_tropicalRadon`: Radon ∘ Adjoint ∘ Radon = Radon on H.
- `tropicalAdjoint_tropicalRadon_tropicalAdjoint`: Adjoint ∘ Radon ∘ Adjoint = Adjoint.
- `tropicalRadon_injective_on_normalForm`: Injectivity on the normal-form class.
- `tropicalRadon_reconstruct_normalForm`: Certified reconstruction for normal forms.
- `mem_range_tropicalRadon_iff_supportData`: Exact image characterization.
- `exists_minimal_separating_subfamily`: Existence of a minimal determining family.

## Convention

We use the **sup-plus** convention throughout:
  Radon_H(f)(h) = sup_{x ∈ X} (f(x) + h(x))

This is the tropical analogue of the Legendre–Fenchel transform, and we prove
duality with the **inf-minus** adjoint:
  Adjoint_H(F)(x) = inf_{h ∈ H} (F(h) - h(x))
-/


noncomputable section

open Finset Function

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-! ## Core Definitions -/





/-! ## The Galois Connection (Theorem B core)

The tropical Radon transform and its adjoint form a Galois connection:
  (∀ h ∈ H, Radon(f)(h) ≤ F(h)) ↔ (∀ x, f(x) ≤ Adjoint(F)(x))

This is the finite idempotent analogue of Legendre–Fenchel duality.
-/


/-! ## Monotonicity -/



/-! ## Closure Properties -/

/-
f ≤ Adjoint(Radon(f)): the closure is always above the original.
-/
theorem tropicalAdjoint_tropicalRadon_ge (H : Finset (X → ℤ)) (hH : H.Nonempty)
    (f : X → ℤ) :
    ∀ x, f x ≤ tropicalAdjoint H hH (tropicalRadon H f) x := by
  intro x;
  apply Finset.le_inf';
  exact fun h hh => le_tsub_of_add_le_right ( Finset.le_sup' ( fun x => f x + h x ) ( Finset.mem_univ x ) )

/-
Radon(Adjoint(F))(h) ≤ F(h) for h ∈ H.
-/

/-
Radon ∘ Adjoint ∘ Radon = Radon on H.
-/

/-
Adjoint ∘ Radon ∘ Adjoint = Adjoint.
-/
theorem tropicalAdjoint_tropicalRadon_tropicalAdjoint (H : Finset (X → ℤ)) (hH : H.Nonempty)
    (F : (X → ℤ) → ℤ) :
    tropicalAdjoint H hH (tropicalRadon H (tropicalAdjoint H hH F)) =
      tropicalAdjoint H hH F := by
  ext x;
  refine' le_antisymm _ _;
  · unfold tropicalAdjoint tropicalRadon;
    simp +decide [ Finset.inf'_le_iff ];
    intro h hh; use h; simp +decide [ hh ] ;
    exact fun y => by linarith [ Finset.inf'_le ( fun h => F h - h y ) hh ] ;
  · exact tropicalAdjoint_tropicalRadon_ge _ _ _ _

/-! ## Theorem A: Injectivity on Normal Forms -/


/-! ## Theorem B: Image Characterization -/


/-! ## Theorem D: Certified Reconstruction -/



/-! ## Theorem C: Minimal Separating Subfamily -/


/-
The Radon transform determines normal-form functions: any B ⊆ H that is nonempty
    makes the Radon transform injective on B-normal-form functions.
-/

/-
There exists an inclusion-minimal nonempty subfamily B ⊆ H such that every element
    of H can be dropped from B while preserving the normal-form injectivity property,
    but B itself cannot be further reduced. Concretely, B is the result of greedily
    removing redundant directions.
-/


theorem solution(H : Finset (X → ℤ)) (hH : H.Nonempty)
    (F : (X → ℤ) → ℤ) :
    (∃ f, IsTropicalNormalForm H hH f ∧ ∀ h ∈ H, tropicalRadon H f h = F h) ↔
    IsTropicalSupportData H hH F := by
  constructor;
  · rintro ⟨ f, hf, hF ⟩;
    -- Since Radon f = F on H, we have Adjoint(F) = Adjoint(Radon f) = f (by hf).
    have h_adj : tropicalAdjoint H hH F = f := by
      have h_adj : tropicalAdjoint H hH (tropicalRadon H f) = tropicalAdjoint H hH F := by
        unfold tropicalAdjoint; aesop;
      exact h_adj ▸ hf;
    unfold IsTropicalSupportData; aesop;
  · intro hF
    use tropicalAdjoint H hH F;
    exact ⟨ tropicalAdjoint_tropicalRadon_tropicalAdjoint H hH F, hF ⟩
