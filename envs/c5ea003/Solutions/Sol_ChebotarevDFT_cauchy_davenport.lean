-- Prove2me | solution 1 for ChebotarevDFT.cauchy_davenport
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:06:50.352984+00:00
-- url     : https://prove2.me/submissions/015fecba-fa2d-4851-9f41-f0ded81d7ded

-- Sol generated from Novelty/ChebotarevCauchyDavenport.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevCauchyDavenport
import Definitions.Def_Novelty_ChebotarevUncertainty
import Theorems.Thm_ChebotarevDFT_dft_conv
import Theorems.Thm_ChebotarevDFT_exists_supported_vanishing
import Theorems.Thm_ChebotarevDFT_mem_supp
import Theorems.Thm_ChebotarevDFT_uncertainty
/-
# From Chebotarev to Cauchy–Davenport

A Fourier-analytic proof of the Cauchy–Davenport theorem, obtained from the prime-order
uncertainty principle `ChebotarevDFT.uncertainty` (which in turn rests on Chebotarev's theorem
about the nonsingularity of the square submatrices of the DFT matrix).

The route is: Chebotarev ⟹ uncertainty principle ⟹ Cauchy–Davenport, i.e. an algebraic
statement about cyclotomic fields controls an additive-combinatorial one.  (Mathlib contains a
different, combinatorial proof of Cauchy–Davenport; the point here is the bridge.)
-/

open ChebotarevDFT

open Finset Complex ZMod
open scoped ZMod Pointwise

variable {p : ℕ} [NeZero p]

/-! ## Convolution -/



theorem supp_conv_subset (f g : ZMod p → ℂ) : supp (conv f g) ⊆ supp f + supp g := by
  classical
  intro x hx
  rw [mem_supp, conv] at hx
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  refine Finset.mem_add.mpr ⟨y, ?_, x - y, ?_, by ring⟩ <;> rw [mem_supp]
  · exact left_ne_zero_of_mul hy
  · exact right_ne_zero_of_mul hy

/-! ## Two counting lemmas -/

theorem inter_nonempty_of_card (X Y : Finset (ZMod p)) (h : p < X.card + Y.card) :
    (X ∩ Y).Nonempty := by
  rw [← Finset.card_pos]
  have hle : (X ∪ Y).card ≤ p := by
    simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ (X ∪ Y))
  have := Finset.card_inter_add_card_union X Y
  omega

/-! ## Cauchy–Davenport -/



open ChebotarevDFT in
theorem solution(hp : p.Prime) (A B : Finset (ZMod p))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card := by
  classical
  have hApos : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hBpos : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hAle : A.card ≤ p := by simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ A)
  have hBle : B.card ≤ p := by simpa [ZMod.card] using Finset.card_le_card (Finset.subset_univ B)
  by_cases hcase : A.card + B.card ≤ p + 1
  · -- the interesting case: build a function supported in `A + B`
    obtain ⟨T, -, hTcard⟩ := Finset.exists_subset_card_eq
      (show A.card + B.card - 2 ≤ (Finset.univ : Finset (ZMod p)).card by simp [ZMod.card]; omega)
    obtain ⟨SA, hSAsub, hSAcard⟩ := Finset.exists_subset_card_eq
      (show A.card - 1 ≤ T.card by omega)
    set SB := T \ SA with hSB
    have hSBcard : SB.card = B.card - 1 := by
      rw [hSB, Finset.card_sdiff, Finset.inter_eq_left.mpr hSAsub, hTcard, hSAcard]
      omega
    obtain ⟨f, hf0, hfsupp, hfvan⟩ := exists_supported_vanishing A SA (by omega)
    obtain ⟨g, hg0, hgsupp, hgvan⟩ := exists_supported_vanishing B SB (by omega)
    -- supports
    have hsuppf : supp f ⊆ A := fun x hx => by
      by_contra h; exact (mem_supp.mp hx) (hfsupp x h)
    have hsuppg : supp g ⊆ B := fun x hx => by
      by_contra h; exact (mem_supp.mp hx) (hgsupp x h)
    -- the convolution is nonzero
    have hcf : p + 1 ≤ (supp f).card + (supp (𝓕 f)).card := uncertainty hp f hf0
    have hcg : p + 1 ≤ (supp g).card + (supp (𝓕 g)).card := uncertainty hp g hg0
    have hcf' : (supp f).card ≤ A.card := Finset.card_le_card hsuppf
    have hcg' : (supp g).card ≤ B.card := Finset.card_le_card hsuppg
    have hinter : (supp (𝓕 f) ∩ supp (𝓕 g)).Nonempty := by
      refine inter_nonempty_of_card _ _ ?_
      omega
    obtain ⟨t, ht⟩ := hinter
    rw [Finset.mem_inter, mem_supp, mem_supp] at ht
    have hconv0 : conv f g ≠ 0 := by
      intro h
      have : 𝓕 (conv f g) t = 0 := by rw [h]; simp
      rw [dft_conv] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact ht.1 h'
      · exact ht.2 h'
    -- the transform of the convolution vanishes on `T`
    have hTvan : T ⊆ (supp (𝓕 (conv f g)))ᶜ := by
      intro s hs
      simp only [Finset.mem_compl, mem_supp, not_not, dft_conv]
      by_cases h : s ∈ SA
      · rw [hfvan s h, zero_mul]
      · rw [hgvan s (Finset.mem_sdiff.mpr ⟨hs, h⟩), mul_zero]
    have hcard2 : (supp (𝓕 (conv f g))).card ≤ p - (A.card + B.card - 2) := by
      have hle := Finset.card_le_card hTvan
      rw [Finset.card_compl, ZMod.card, hTcard] at hle
      have h3 : (supp (𝓕 (conv f g))).card ≤ p := by
        simpa [ZMod.card] using
          Finset.card_le_card (Finset.subset_univ (supp (𝓕 (conv f g))))
      omega
    have hsuppconv : (supp (conv f g)).card ≤ (A + B).card := by
      refine Finset.card_le_card (subset_trans (supp_conv_subset f g) ?_)
      exact Finset.add_subset_add hsuppf hsuppg
    have hunc := uncertainty hp (conv f g) hconv0
    omega
  · -- the trivial case: `A + B` is everything
    have hall : (A + B) = Finset.univ := by
      refine Finset.eq_univ_of_forall fun x => ?_
      have hY : (Finset.image (fun b => x - b) B).card = B.card :=
        Finset.card_image_of_injective _ (fun u v h => by
          have : -u = -v := by
            simpa [sub_eq_add_neg] using congrArg (fun z => z - x) h
          simpa using congrArg Neg.neg this)
      obtain ⟨a, ha⟩ := inter_nonempty_of_card A (Finset.image (fun b => x - b) B) (by omega)
      rw [Finset.mem_inter, Finset.mem_image] at ha
      obtain ⟨haA, b, hbB, hb⟩ := ha
      exact Finset.mem_add.mpr ⟨a, haA, b, hbB, by rw [← hb]; ring⟩
    rw [hall, Finset.card_univ, ZMod.card]
    exact min_le_left _ _
