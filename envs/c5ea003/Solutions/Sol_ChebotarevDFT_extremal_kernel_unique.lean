-- Prove2me | solution 1 for ChebotarevDFT.extremal_kernel_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:06:52.91852+00:00
-- url     : https://prove2.me/submissions/344225ed-5f89-4927-81e1-ce100362de17

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
theorem solution(hp : p.Prime) (A S : Finset (ZMod p))
    (hcard : A.card = S.card + 1) (f g : ZMod p → ℂ)
    (hf : ∀ x ∉ A, f x = 0) (hg : ∀ x ∉ A, g x = 0)
    (hfv : ∀ s ∈ S, 𝓕 f s = 0) (hgv : ∀ s ∈ S, 𝓕 g s = 0) (hf0 : f ≠ 0) :
    ∃ c : ℂ, g = c • f := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hf0
  have hfa : f a₀ ≠ 0 := ha₀
  have ha₀A : a₀ ∈ A := by
    by_contra h
    exact ha₀ (by simpa using hf a₀ h)
  refine ⟨g a₀ / f a₀, ?_⟩
  set c : ℂ := g a₀ / f a₀ with hc
  set h : ZMod p → ℂ := g - c • f with hh
  have hha₀ : h a₀ = 0 := by
    simp only [hh, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc]
    field_simp [hfa]
    ring
  have hsupp : supp h ⊆ A.erase a₀ := by
    intro x hx
    rw [mem_supp] at hx
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · rintro rfl; exact hx hha₀
    · by_contra hxA
      exact hx (by simp [hh, hf x hxA, hg x hxA])
  have hdft : 𝓕 h = 𝓕 g - c • 𝓕 f := by simp [hh]
  have hzero : h = 0 := by
    by_contra hne
    have hc1 : (supp h).card ≤ S.card := by
      have := Finset.card_le_card hsupp
      rw [Finset.card_erase_of_mem ha₀A] at this
      omega
    have hSsub : S ⊆ (supp (𝓕 h))ᶜ := by
      intro s hs
      simp only [Finset.mem_compl, mem_supp, not_not, hdft]
      simp [hfv s hs, hgv s hs]
    have hc2 : (supp (𝓕 h)).card ≤ p - S.card := by
      have h1 := Finset.card_le_card hSsub
      rw [Finset.card_compl, ZMod.card] at h1
      have h2 : (supp (𝓕 h)).card ≤ p := by
        simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ (supp (𝓕 h)))
      omega
    have hSp : S.card ≤ p := by
      simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ S)
    have := uncertainty hp h hne
    omega
  have := sub_eq_zero.mp (by simpa [hh] using hzero)
  exact this
