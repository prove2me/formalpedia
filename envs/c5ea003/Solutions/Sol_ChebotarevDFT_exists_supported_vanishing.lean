-- Prove2me | solution 1 for ChebotarevDFT.exists_supported_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:56:56.749669+00:00
-- url     : https://prove2.me/submissions/7dd01c28-f420-47d7-b125-7bc431c7c7d0

-- Sol generated from Novelty/ChebotarevUncertainty.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Definitions.Def_Novelty_ChebotarevUncertainty
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



/-! ## The uncertainty principle -/


/-! ## Sharpness -/








/-! ## Exact recovery of sparse signals -/



/-! ## Primality is essential -/



open ChebotarevDFT in
theorem solution(A S : Finset (ZMod p)) (hcard : A.card = S.card + 1) :
    ∃ f : ZMod p → ℂ, f ≠ 0 ∧ (∀ x, x ∉ A → f x = 0) ∧ ∀ s ∈ S, 𝓕 f s = 0 := by
  classical
  set m := S.card with hm
  set eA : {x // x ∈ A} ≃ Fin (m + 1) := A.equivFin.trans (finCongr hcard) with heA
  set eS : {x // x ∈ S} ≃ Fin m := S.equivFin with heS
  set α : Fin (m + 1) → ZMod p := fun i => (eA.symm i : ZMod p) with hα
  set σ : Fin m → ZMod p := fun j => (eS.symm j : ZMod p) with hσ
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := Matrix.of fun i j =>
    if h : (j : ℕ) < m then ZMod.stdAddChar (-(α i * σ ⟨j, h⟩)) else 0 with hM
  have hdet : M.det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero (Fin.last m)
    intro i
    simp [hM]
  obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  refine ⟨fun x => if h : x ∈ A then v (eA ⟨x, h⟩) else 0, ?_, ?_, ?_⟩
  · intro hzero
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    apply hi
    have := congrFun hzero (α i)
    simpa [hα, Subtype.coe_eta] using this
  · intro x hx; simp [hx]
  · intro s hs
    have hsj : s = σ (eS ⟨s, hs⟩) := by simp [hσ]
    set j : Fin m := eS ⟨s, hs⟩ with hj
    have hj' : ((⟨j, by omega⟩ : Fin (m + 1)) : ℕ) < m := j.isLt
    have hvj := congrFun hvM (⟨j, by omega⟩ : Fin (m + 1))
    rw [ZMod.dft_apply]
    rw [← Finset.sum_subset (Finset.subset_univ A) (by intro x _ hx; simp [hx])]
    rw [← Finset.sum_coe_sort A (fun x => ZMod.stdAddChar (-(x * s)) •
      (if h : x ∈ A then v (eA ⟨x, h⟩) else 0))]
    rw [← Equiv.sum_comp eA.symm]
    simp only [Matrix.vecMul, dotProduct, hM, Matrix.of_apply, Pi.zero_apply] at hvj
    rw [← hvj]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hee : (eA (eA.symm i)) = i := by simp
    simp only [dif_pos (eA.symm i).2, hee, smul_eq_mul]
    rw [dif_pos hj', mul_comm]
    congr 2
    rw [← hsj]
