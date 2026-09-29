-- Prove2me | solution 1 for ChebotarevDFT.uncertainty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:05:12.169092+00:00
-- url     : https://prove2.me/submissions/578eb857-f7fb-41a5-8e66-9c6df4aa0745

-- Sol generated from Novelty/ChebotarevUncertainty.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Definitions.Def_Novelty_ChebotarevUncertainty
import Theorems.Thm_ChebotarevDFT_det_ne_zero
import Theorems.Thm_ChebotarevDFT_mem_supp
/-
# Consequences of Chebotarev's theorem: the prime-order uncertainty principle

Building on `ChebotarevDFT.det_ne_zero` (every square submatrix of the `p × p` DFT matrix is
nonsingular for `p` prime) we derive:

* `ChebotarevDFT.uncertainty` : Tao's uncertainty principle, `#supp Φ + #supp (𝓕 Φ) ≥ p + 1`
  for every nonzero `Φ : ZMod p → ℂ`;
* `ChebotarevDFT.uncertainty_sharp_delta` : the bound is attained by a Dirac mass;
* `ChebotarevDFT.sparse_recovery` : a `k`-sparse signal on `ZMod p` is determined by *any*
  `2 * k` of its Fourier coefficients (exact recovery in compressed sensing);
* `ChebotarevDFT.singular_submatrix_of_composite` : for the composite modulus `4` the analogous
  statement fails, so primality is essential.
-/

open ChebotarevDFT

open Finset Matrix Complex ZMod
open scoped ZMod

variable {p : ℕ} [NeZero p]



/-! ## The standard additive character as a power of a primitive root -/

/-- `stdAddChar (-1)` is a primitive `p`-th root of unity. -/
theorem isPrimitiveRoot_stdAddChar (p : ℕ) [NeZero p] :
    IsPrimitiveRoot (ZMod.stdAddChar (-1 : ZMod p)) p := by
  have h : ZMod.stdAddChar (-1 : ZMod p)
      = Complex.exp (2 * Real.pi * Complex.I * (-1 : ℤ) / p) := by
    rw [← ZMod.stdAddChar_coe]; norm_num
  rw [h, show (2 * (Real.pi : ℂ) * Complex.I * (-1 : ℤ) / p)
      = -(2 * Real.pi * Complex.I / p) by push_cast; ring, Complex.exp_neg]
  exact (Complex.isPrimitiveRoot_exp p (NeZero.ne p)).inv

/-- The kernel of the discrete Fourier transform is a power of `stdAddChar (-1)`. -/
theorem stdAddChar_neg_mul (p : ℕ) [NeZero p] (x k : ZMod p) :
    ZMod.stdAddChar (-(x * k)) = (ZMod.stdAddChar (-1 : ZMod p)) ^ (x.val * k.val) := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  push_cast [nsmul_eq_mul]
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  ring

/-! ## The uncertainty principle -/


/-! ## Sharpness -/








/-! ## Exact recovery of sparse signals -/



/-! ## Primality is essential -/



open ChebotarevDFT in
theorem solution(hp : p.Prime) (Φ : ZMod p → ℂ) (hΦ : Φ ≠ 0) :
    p + 1 ≤ (supp Φ).card + (supp (𝓕 Φ)).card := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push_neg at hcon
  set A := supp Φ with hA
  set k := A.card with hk
  have hk1 : 1 ≤ k := by
    rw [hk, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hΦ
    exact ⟨x, mem_supp.mpr hx⟩
  have hcompl : k ≤ ((supp (𝓕 Φ))ᶜ).card := by
    rw [Finset.card_compl, ZMod.card]
    omega
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hcompl
  -- enumerate the two sets
  set eA : {x // x ∈ A} ≃ Fin k := A.equivFin with heA
  set eB : {x // x ∈ B} ≃ Fin k := B.equivFin.trans (finCongr hBcard) with heB
  set α : Fin k → ZMod p := fun i => (eA.symm i : ZMod p) with hα
  set β : Fin k → ZMod p := fun j => (eB.symm j : ZMod p) with hβ
  have hαmem : ∀ i, α i ∈ A := fun i => (eA.symm i).2
  have hβmem : ∀ j, β j ∈ B := fun j => (eB.symm j).2
  have hαinj : Function.Injective α := by
    intro i₁ i₂ h
    exact eA.symm.injective (Subtype.ext h)
  have hβinj : Function.Injective β := by
    intro j₁ j₂ h
    exact eB.symm.injective (Subtype.ext h)
  -- the associated integer data
  set a : Fin k → ℕ := fun i => (α i).val with ha
  set b : Fin k → ℕ := fun j => (β j).val with hb
  have hainj : Function.Injective a := fun i₁ i₂ h => hαinj ((ZMod.val_injective p) h)
  have hbinj : Function.Injective b := fun j₁ j₂ h => hβinj ((ZMod.val_injective p) h)
  have halt : ∀ i, a i < p := fun i => ZMod.val_lt _
  have hblt : ∀ j, b j < p := fun j => ZMod.val_lt _
  -- Chebotarev: the submatrix is nonsingular
  have hdet := det_ne_zero (n := k) (p := p) hp (isPrimitiveRoot_stdAddChar p) a b
    hainj halt hbinj hblt
  -- the restriction of `Φ` is in the kernel
  set v : Fin k → ℂ := fun i => Φ (α i) with hv
  have hvec : v ᵥ* (Matrix.of fun i j : Fin k =>
      (ZMod.stdAddChar (-1 : ZMod p)) ^ (a i * b j)) = 0 := by
    funext j
    have hsum : ∑ i : Fin k, Φ (α i) * (ZMod.stdAddChar (-1 : ZMod p)) ^ (a i * b j)
        = 𝓕 Φ (β j) := by
      have h1 : ∑ i : Fin k, Φ (α i) * (ZMod.stdAddChar (-1 : ZMod p)) ^ (a i * b j)
          = ∑ x ∈ A, Φ x * (ZMod.stdAddChar (-1 : ZMod p)) ^ (x.val * (β j).val) := by
        rw [← Finset.sum_coe_sort A
          (fun x => Φ x * (ZMod.stdAddChar (-1 : ZMod p)) ^ (x.val * (β j).val))]
        simpa [hα, ha, hb] using Equiv.sum_comp eA.symm
          (fun y : {x // x ∈ A} =>
            Φ (y : ZMod p) * (ZMod.stdAddChar (-1 : ZMod p)) ^ ((y : ZMod p).val * (β j).val))
      rw [h1, ZMod.dft_apply]
      rw [← Finset.sum_subset (Finset.subset_univ A)]
      · exact Finset.sum_congr rfl fun x _ => by
          rw [stdAddChar_neg_mul, smul_eq_mul, mul_comm]
      · intro x _ hx
        have : Φ x = 0 := by
          by_contra h
          exact hx (mem_supp.mpr h)
        simp [this]
    have hzero : 𝓕 Φ (β j) = 0 := by
      have := hBsub (hβmem j)
      simp only [Finset.mem_compl] at this
      by_contra h
      exact this (mem_supp.mpr h)
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply, hv]
    exact hsum.trans hzero
  have hv0 : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  have : Φ (α ⟨0, hk1⟩) = 0 := congrFun hv0 ⟨0, hk1⟩
  exact (mem_supp.mp (hαmem ⟨0, hk1⟩)) this
