-- Prove2me | solution 1 for ChebotarevDFT.sparse_recovery_optimal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:06:54.22195+00:00
-- url     : https://prove2.me/submissions/bd17f312-5f47-4c8a-8efa-68f0cc6a7022

-- Sol generated from Novelty/ChebotarevUncertainty.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Definitions.Def_Novelty_ChebotarevUncertainty
import Theorems.Thm_ChebotarevDFT_exists_supported_vanishing
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



/-! ## The uncertainty principle -/


/-! ## Sharpness -/








/-! ## Exact recovery of sparse signals -/



/-! ## Primality is essential -/



open ChebotarevDFT in
theorem solution(k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ p)
    (S : Finset (ZMod p)) (hS : S.card = 2 * k - 1) :
    ∃ f g : ZMod p → ℂ, f ≠ g ∧ (supp f).card ≤ k ∧ (supp g).card ≤ k ∧
      ∀ s ∈ S, 𝓕 f s = 𝓕 g s := by
  classical
  obtain ⟨A, -, hAcard⟩ := Finset.exists_subset_card_eq
    (show 2 * k ≤ (Finset.univ : Finset (ZMod p)).card by simpa [ZMod.card] using hk)
  obtain ⟨h, hh0, hhsupp, hhvan⟩ := exists_supported_vanishing A S (by omega)
  obtain ⟨A₁, hA₁sub, hA₁card⟩ := Finset.exists_subset_card_eq (show k ≤ A.card by omega)
  set A₂ : Finset (ZMod p) := A \ A₁ with hA₂
  have hA₂card : A₂.card = k := by
    rw [hA₂, Finset.card_sdiff, Finset.inter_eq_left.mpr hA₁sub, hAcard, hA₁card]
    omega
  refine ⟨fun x => if x ∈ A₁ then h x else 0,
    fun x => -(if x ∈ A₂ then h x else 0), ?_, ?_, ?_, ?_⟩
  · -- the difference of the two signals is `h ≠ 0`
    intro hfg
    apply hh0
    funext x
    have := congrFun hfg x
    by_cases hx : x ∈ A
    · by_cases hx1 : x ∈ A₁
      · have hx2 : x ∉ A₂ := by simp [hA₂, hx1]
        simpa [hx1, hx2] using this
      · have hx2 : x ∈ A₂ := by simp [hA₂, hx, hx1]
        simp only [if_neg hx1, if_pos hx2] at this
        simpa using this.symm
    · simp [hhsupp x hx]
  · refine le_trans (Finset.card_le_card ?_) (le_of_eq hA₁card)
    intro x hx
    rw [mem_supp] at hx
    by_contra hx1
    exact hx (by simp [hx1])
  · refine le_trans (Finset.card_le_card ?_) (le_of_eq hA₂card)
    intro x hx
    rw [mem_supp] at hx
    by_contra hx2
    exact hx (by simp [hx2])
  · intro s hs
    have hsum : (fun x => if x ∈ A₁ then h x else 0)
        - (fun x => -(if x ∈ A₂ then h x else 0)) = h := by
      funext x
      by_cases hx : x ∈ A
      · by_cases hx1 : x ∈ A₁
        · have hx2 : x ∉ A₂ := by simp [hA₂, hx1]
          simp [hx1, hx2]
        · have hx2 : x ∈ A₂ := by simp [hA₂, hx, hx1]
          simp [hx1, hx2]
      · have hx1 : x ∉ A₁ := fun hc => hx (hA₁sub hc)
        have hx2 : x ∉ A₂ := by simp [hA₂, hx]
        simp [hx1, hx2, hhsupp x hx]
    have hdft : 𝓕 (fun x => if x ∈ A₁ then h x else 0) s
        - 𝓕 (fun x => -(if x ∈ A₂ then h x else 0)) s = 0 := by
      have : 𝓕 ((fun x => if x ∈ A₁ then h x else 0)
          - (fun x => -(if x ∈ A₂ then h x else 0))) s = 0 := by
        rw [hsum]; exact hhvan s hs
      simpa using this
    linear_combination hdft
