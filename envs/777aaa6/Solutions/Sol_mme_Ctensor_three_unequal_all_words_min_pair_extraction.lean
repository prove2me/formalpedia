-- Prove2me | solution 1 for mme_Ctensor_three_unequal_all_words_min_pair_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:38:52.450608+00:00
-- url     : https://prove2.me/submissions/dd3144b8-dc7f-42ff-838f-dd1459ac183a

import Theorems.Thm_mme_Ctensor_three_unequal_word_induced_matching_extraction
import Theorems.Thm_mme_rectangular_MM_support_min_pair_matching
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {X Y Z : TensorObj K 3}
    {H0 H1 H2 v0 v1 v2 : ℕ}
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (h0 : 0 < H0) (h1 : 0 < H1) (h2 : 0 < H2) (R : ℕ) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((threeStarCyclicProduct X Y Z).kronPow R) ∧
      (((min ((H0 * H1) ^ R)
          (min ((H0 * H2) ^ R) ((H1 * H2) ^ R)) : ℕ) : ℝ) / 2) *
        Real.exp (-100 * Real.sqrt
          (Real.log (((min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 : ℕ) : ℝ)))) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = (v0 * v1 * v2) ^ R) := by
  classical
  let w0 : Fin (H0 ^ R) ≃ (Fin R → Fin H0) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  let w1 : Fin (H1 ^ R) ≃ (Fin R → Fin H1) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  let w2 : Fin (H2 ^ R) ≃ (Fin R → Fin H2) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  obtain ⟨E, hxy, hyz, hzx, hinduced, hcard⟩ :=
    mme_rectangular_MM_support_min_pair_matching (H0 ^ R) (H1 ^ R) (H2 ^ R)
      (pow_pos h0 R) (pow_pos h1 R) (pow_pos h2 R)
  obtain ⟨a, b, c, hrestrict, hvolume⟩ :=
    mme_Ctensor_three_unequal_word_induced_matching_extraction certX certY certZ
      w0 w0.injective w1 w1.injective w2 w2.injective E hxy hyz hzx hinduced
  refine ⟨E.card, a, b, c, hrestrict, ?_, hvolume⟩
  simpa only [mul_pow] using hcard
