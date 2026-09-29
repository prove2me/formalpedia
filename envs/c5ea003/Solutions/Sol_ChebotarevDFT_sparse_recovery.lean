-- Prove2me | solution 1 for ChebotarevDFT.sparse_recovery
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:06:53.468176+00:00
-- url     : https://prove2.me/submissions/fc400229-7527-4f00-ab2e-0c3a710a81ce

-- Sol generated from Novelty/ChebotarevUncertainty.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Definitions.Def_Novelty_ChebotarevUncertainty
import Theorems.Thm_ChebotarevDFT_mem_supp
import Theorems.Thm_ChebotarevDFT_uncertainty
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
theorem solution(hp : p.Prime) {k : ℕ} (Φ Ψ : ZMod p → ℂ)
    (hΦ : (supp Φ).card ≤ k) (hΨ : (supp Ψ).card ≤ k)
    (S : Finset (ZMod p)) (hS : 2 * k ≤ S.card) (heq : ∀ s ∈ S, 𝓕 Φ s = 𝓕 Ψ s) :
    Φ = Ψ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra hne
  have hsub : supp (Φ - Ψ) ⊆ supp Φ ∪ supp Ψ := by
    intro x hx
    rw [mem_supp] at hx
    simp only [Finset.mem_union, mem_supp]
    by_contra h
    push_neg at h
    exact hx (by simp [Pi.sub_apply, h.1, h.2])
  have hcard1 : (supp (Φ - Ψ)).card ≤ 2 * k :=
    le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) (by omega))
  have hdftsub : 𝓕 (Φ - Ψ) = 𝓕 Φ - 𝓕 Ψ := by
    simp
  have hSdisj : S ⊆ (supp (𝓕 (Φ - Ψ)))ᶜ := by
    intro s hs
    simp only [Finset.mem_compl, mem_supp, not_not, hdftsub]
    simp [heq s hs]
  have hcard2 : (supp (𝓕 (Φ - Ψ))).card ≤ p - 2 * k := by
    have h1 : S.card ≤ ((supp (𝓕 (Φ - Ψ)))ᶜ).card := Finset.card_le_card hSdisj
    rw [Finset.card_compl, ZMod.card] at h1
    have h2 : (supp (𝓕 (Φ - Ψ))).card ≤ p := by
      simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ (supp (𝓕 (Φ - Ψ))))
    omega
  have hSp : S.card ≤ p := by
    simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ S)
  have hnz : Φ - Ψ ≠ 0 := sub_ne_zero_of_ne hne
  have hunc := uncertainty hp (Φ - Ψ) hnz
  omega
