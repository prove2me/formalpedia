-- Prove2me | solution 1 for ChebotarevDFT.uncertainty_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:06:54.819859+00:00
-- url     : https://prove2.me/submissions/9309f18a-3b0c-437f-bd0e-2706a3871fbd

-- Sol generated from Novelty/ChebotarevUncertainty.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Definitions.Def_Novelty_ChebotarevUncertainty
import Theorems.Thm_ChebotarevDFT_exists_supported_vanishing
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
theorem solution(hp : p.Prime) (A : Finset (ZMod p)) (hA : A.Nonempty) :
    ∃ f : ZMod p → ℂ, supp f = A ∧ (supp f).card + (supp (𝓕 f)).card = p + 1 := by
  classical
  have hApos : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hAle : A.card ≤ p := by simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ A)
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq
    (show A.card - 1 ≤ (Finset.univ : Finset (ZMod p)).card by simp [ZMod.card]; omega)
  obtain ⟨f, hf0, hfsupp, hfvan⟩ := exists_supported_vanishing A S (by omega)
  have hsub : supp f ⊆ A := by
    intro x hx
    by_contra h
    exact (mem_supp.mp hx) (hfsupp x h)
  have h1 : (supp f).card ≤ A.card := Finset.card_le_card hsub
  have hSsub : S ⊆ (supp (𝓕 f))ᶜ := by
    intro s hs
    simp only [Finset.mem_compl, mem_supp, not_not]
    exact hfvan s hs
  have h2 : (supp (𝓕 f)).card ≤ p - (A.card - 1) := by
    have hle := Finset.card_le_card hSsub
    rw [Finset.card_compl, ZMod.card, hScard] at hle
    have h3 : (supp (𝓕 f)).card ≤ p := by
      simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ (supp (𝓕 f)))
    omega
  have hunc := uncertainty hp f hf0
  have hcards : (supp f).card = A.card := by omega
  exact ⟨f, Finset.eq_of_subset_of_card_le hsub (le_of_eq hcards.symm), by omega⟩
