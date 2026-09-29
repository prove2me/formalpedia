-- Prove2me | Definitions.Def_Shared_FourierFiniteAbelian
-- name    : Shared_FourierFiniteAbelian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:49:35.837385+00:00
-- url     : https://prove2.me/theorems/171012bf-b914-46e8-b2ae-5210dd6731ef
-- title:
--   Aether Catalog definitions — Shared_FourierFiniteAbelian
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.FourierFiniteAbelian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/FourierFiniteAbelian.lean by skeleton subtraction
import Mathlib
/-
# Fourier analysis on finite abelian groups

This file develops the discrete Fourier transform (DFT) on an arbitrary finite abelian
group `G`, viewed as the decomposition of the regular representation into the characters
of `G` (equivalently, as the expansion in the Pontryagin dual `AddChar G ℂ`).

Main results:

* `FourierFA.sum_char_sub` : the orthogonality relation `∑ ψ, ψ (x - y) = |G| ⬝ [x = y]`.
* `FourierFA.dft_inversion` : Fourier inversion `f = idft (dft f)`.
* `FourierFA.parseval` : `∑_ψ f̂ ψ * conj (ĝ ψ) = |G| * ∑_x f x * conj (g x)`.
* `FourierFA.parseval_norm` : `∑_ψ ‖f̂ ψ‖² = |G| * ∑_x ‖f x‖²`.
* `FourierFA.dft_conv` : the convolution theorem `(f ∗ g)^ = f̂ · ĝ`.
* `FourierFA.dft_injective`, `FourierFA.dftEquiv` : the DFT is a linear equivalence.
* `FourierFA.uncertainty` : the Donoho–Stark uncertainty principle
  `|supp f| * |supp f̂| ≥ |G|` for `f ≠ 0`.
* `FourierFA.uncertainty_sharp_delta` : the bound is attained (Dirac deltas).
* `FourierFA.sum_char_mul_conj` : orthogonality of characters summed over the group.
* `FourierFA.idft_inversion`, `FourierFA.dftEquiv` : `idft` is a two-sided inverse, so the DFT
  is a linear equivalence with explicit inverse.
* `FourierFA.dft_dft` : `F² = |G| ⬝ reflection`, via Pontryagin's canonical embedding.
-/


open Finset Fintype ComplexConjugate
open scoped BigOperators

namespace FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Definitions -/

/-- The discrete Fourier transform of `f : G → ℂ`, indexed by the Pontryagin dual of `G`. -/
noncomputable def dft (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ := ∑ x, conj (ψ x) * f x

/-- The inverse discrete Fourier transform. -/
noncomputable def idft (F : AddChar G ℂ → ℂ) (x : G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ ψ : AddChar G ℂ, ψ x * F ψ

/-- Convolution of two functions on `G`. -/
noncomputable def conv (f g : G → ℂ) (x : G) : ℂ := ∑ y, f y * g (x - y)

/-- The support of `f`, as a `Finset`. -/
noncomputable def supp (f : G → ℂ) : Finset G := Finset.univ.filter (fun x => f x ≠ 0)


/-! ## Orthogonality -/

/-- Orthogonality of characters, in the "dual" form: summing a fixed group element over all
characters. -/
lemma sum_char_sub (x y : G) :
    ∑ ψ : AddChar G ℂ, ψ x * conj (ψ y) = if x = y then (Fintype.card G : ℂ) else 0 := by
  have h : ∀ ψ : AddChar G ℂ, ψ x * conj (ψ y) = ψ (x - y) := by
    intro ψ
    rw [sub_eq_add_neg, ψ.map_add_eq_mul, AddChar.map_neg_eq_conj]
  simp_rw [h]
  rw [AddChar.sum_apply_eq_ite (x - y)]
  simp [sub_eq_zero]

omit [DecidableEq G] in
/-- Orthogonality of characters, in the "primal" form: summing over the group. -/
lemma sum_char_mul_conj (ψ χ : AddChar G ℂ) :
    ∑ x : G, ψ x * conj (χ x) = if ψ = χ then (Fintype.card G : ℂ) else 0 := by
  classical
  have h : ∀ x : G, ψ x * conj (χ x) = (ψ - χ) x := by
    intro x
    rw [AddChar.sub_apply' ψ χ x, div_eq_mul_inv, AddChar.inv_apply_eq_conj]
  simp_rw [h]
  rw [AddChar.sum_eq_ite (ψ - χ)]
  simp [sub_eq_zero]

/-! ## Linearity -/


omit [DecidableEq G] in
lemma dft_add (f g : G → ℂ) : dft (f + g) = dft f + dft g := by
  funext ψ; simp [dft, mul_add, Finset.sum_add_distrib]

omit [DecidableEq G] in
lemma dft_smul (c : ℂ) (f : G → ℂ) : dft (c • f) = c • dft f := by
  funext ψ; simp [dft, Finset.mul_sum, mul_left_comm]

/-- The DFT as a `ℂ`-linear map. -/
noncomputable def dftLinear : (G → ℂ) →ₗ[ℂ] (AddChar G ℂ → ℂ) where
  toFun := dft
  map_add' := dft_add
  map_smul' := dft_smul


/-! ## Fourier inversion -/

/-- **Fourier inversion** on a finite abelian group. -/
theorem dft_inversion (f : G → ℂ) : idft (dft f) = f := by
  funext x
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  have key : ∑ ψ : AddChar G ℂ, ψ x * dft f ψ = (Fintype.card G : ℂ) * f x := by
    calc ∑ ψ : AddChar G ℂ, ψ x * dft f ψ
        = ∑ ψ : AddChar G ℂ, ∑ y, (ψ x * conj (ψ y)) * f y := by
          refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [dft, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ y, (∑ ψ : AddChar G ℂ, ψ x * conj (ψ y)) * f y := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => by rw [Finset.sum_mul]
      _ = (Fintype.card G : ℂ) * f x := by
          simp_rw [sum_char_sub]
          rw [Finset.sum_eq_single x]
          · simp
          · intro y _ hy
            simp [Ne.symm hy]
          · intro h; exact absurd (Finset.mem_univ x) h
  rw [idft, key, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]


omit [DecidableEq G] in
/-- The inverse transform really is a right inverse: `dft (idft F) = F`. -/
theorem idft_inversion (F : AddChar G ℂ → ℂ) : dft (idft F) = F := by
  funext χ
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  have key : ∀ x : G, conj (χ x) * idft F x
      = (Fintype.card G : ℂ)⁻¹ * ∑ ψ : AddChar G ℂ, (ψ x * conj (χ x)) * F ψ := by
    intro x
    have hx : ∑ ψ : AddChar G ℂ, (ψ x * conj (χ x)) * F ψ
        = conj (χ x) * ∑ ψ : AddChar G ℂ, ψ x * F ψ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ψ _ => by ring
    rw [idft, hx]
    ring
  calc dft (idft F) χ = ∑ x : G, conj (χ x) * idft F x := rfl
    _ = ∑ x : G, (Fintype.card G : ℂ)⁻¹ * ∑ ψ : AddChar G ℂ, (ψ x * conj (χ x)) * F ψ :=
        Finset.sum_congr rfl fun x _ => key x
    _ = (Fintype.card G : ℂ)⁻¹ * ∑ ψ : AddChar G ℂ, (∑ x : G, ψ x * conj (χ x)) * F ψ := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ψ _ => by rw [Finset.sum_mul]
    _ = F χ := by
        simp_rw [sum_char_mul_conj]
        rw [Finset.sum_eq_single χ]
        · rw [if_pos rfl, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
        · intro ψ _ hψ; simp [hψ]
        · intro h; exact absurd (Finset.mem_univ χ) h

/-- The discrete Fourier transform as a `ℂ`-linear equivalence between functions on `G` and
functions on the Pontryagin dual, with explicit inverse `idft`. -/
noncomputable def dftEquiv : (G → ℂ) ≃ₗ[ℂ] (AddChar G ℂ → ℂ) where
  toFun := dft
  map_add' := dft_add
  map_smul' := dft_smul
  invFun := idft
  left_inv := dft_inversion
  right_inv := idft_inversion



/-! ## Parseval / Plancherel -/



/-! ## The convolution theorem -/


/-! ## Squaring the transform -/


/-! ## The Donoho–Stark uncertainty principle -/



/-! ## Sharpness -/

/-- The Dirac delta at `a`. -/
noncomputable def delta (a : G) : G → ℂ := fun x => if x = a then 1 else 0





end FourierFA


