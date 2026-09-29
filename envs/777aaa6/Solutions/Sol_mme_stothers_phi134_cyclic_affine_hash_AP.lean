-- Prove2me | solution 1 for mme_stothers_phi134_cyclic_affine_hash_AP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:48:59.690021+00:00
-- url     : https://prove2.me/submissions/dd7e17b0-6d23-4c18-9e34-bcdfc0685039

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p)
    (x y z : CyclicExactEdge N alpha beta gamma delta)
    (hsupp : CyclicCoordinatewiseSupported x y z) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset 0 x +
        cyclicAffineHash p N alpha beta gamma delta w shift offset 1 y =
      2 * cyclicAffineHash p N alpha beta gamma delta w shift offset 2 z := by
  have hgrade
      (a : ProfileAddress N) (ha : CoordinatewiseSupported a)
      (j : Fin (2 * N)) :
      (a 0 j).val + (a 1 j).val + (a 2 j).val = 4 := by
    obtain ⟨r, hr⟩ := ha j
    have h0 := congrFun hr (0 : Fin 3)
    have h1 := congrFun hr (1 : Fin 3)
    have h2 := congrFun hr (2 : Fin 3)
    fin_cases r <;>
      simp [addressType, pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢ <;>
      omega
  have hA (j : Fin (2 * N)) :
      (x.1.1.1 0 j).val + (y.1.1.1 1 j).val +
        (z.1.1.1 2 j).val = 4 := by
    simpa [mixedAddress] using
      hgrade (mixedAddress x.1.1 y.1.1 z.1.1) hsupp.1 j
  have hB (j : Fin (2 * N)) :
      (y.2.1.1.1 0 j).val + (z.2.1.1.1 1 j).val +
        (x.2.1.1.1 2 j).val = 4 := by
    simpa [mixedAddress] using
      hgrade (mixedAddress y.2.1.1 z.2.1.1 x.2.1.1) hsupp.2.1 j
  have hC (j : Fin (2 * N)) :
      (z.2.2.1.1 0 j).val + (x.2.2.1.1 1 j).val +
        (y.2.2.1.1 2 j).val = 4 := by
    simpa [mixedAddress] using
      hgrade (mixedAddress z.2.2.1 x.2.2.1 y.2.2.1) hsupp.2.2 j
  have haPoint (j : Fin (2 * N)) :
      ((2 * (x.1.1.1 0 j).val : ℕ) : ZMod p) * w 0 j +
          ((2 * (y.1.1.1 1 j).val : ℕ) : ZMod p) * w 0 j =
        2 * (((4 : ZMod p) - ((z.1.1.1 2 j).val : ZMod p)) * w 0 j) := by
    have hr := congrArg (fun n : ℕ ↦ (n : ZMod p)) (hA j)
    push_cast at hr ⊢
    linear_combination 2 * w 0 j * hr
  have hbPoint (j : Fin (2 * N)) :
      4 * ((4 : ZMod p) - ((x.2.1.1.1 2 j).val : ZMod p)) * w 1 j +
          (-2 * ((2 * (y.2.1.1.1 0 j).val : ℕ) : ZMod p)) * w 1 j =
        2 * (((2 * (z.2.1.1.1 1 j).val : ℕ) : ZMod p) * w 1 j) := by
    have hr := congrArg (fun n : ℕ ↦ (n : ZMod p)) (hB j)
    push_cast at hr ⊢
    linear_combination -4 * w 1 j * hr
  have hcPoint (j : Fin (2 * N)) :
      (-2 * ((2 * (x.2.2.1.1 1 j).val : ℕ) : ZMod p)) * w 2 j +
          4 * ((4 : ZMod p) - ((y.2.2.1.1 2 j).val : ZMod p)) * w 2 j =
        2 * (((2 * (z.2.2.1.1 0 j).val : ℕ) : ZMod p) * w 2 j) := by
    have hr := congrArg (fun n : ℕ ↦ (n : ZMod p)) (hC j)
    push_cast at hr ⊢
    linear_combination -4 * w 2 j * hr
  have ha :
      (∑ j, ((2 * (x.1.1.1 0 j).val : ℕ) : ZMod p) * w 0 j) +
          (∑ j, ((2 * (y.1.1.1 1 j).val : ℕ) : ZMod p) * w 0 j) =
        2 * ∑ j,
          ((4 : ZMod p) - ((z.1.1.1 2 j).val : ZMod p)) * w 0 j := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ haPoint j)
  have hb :
      (∑ j, 4 * ((4 : ZMod p) - ((x.2.1.1.1 2 j).val : ZMod p)) * w 1 j) +
          (∑ j, (-2 * ((2 * (y.2.1.1.1 0 j).val : ℕ) : ZMod p)) * w 1 j) =
        2 * ∑ j,
          ((2 * (z.2.1.1.1 1 j).val : ℕ) : ZMod p) * w 1 j := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ hbPoint j)
  have hc :
      (∑ j, (-2 * ((2 * (x.2.2.1.1 1 j).val : ℕ) : ZMod p)) * w 2 j) +
          (∑ j, 4 * ((4 : ZMod p) - ((y.2.2.1.1 2 j).val : ZMod p)) * w 2 j) =
        2 * ∑ j,
          ((2 * (z.2.2.1.1 0 j).val : ℕ) : ZMod p) * w 2 j := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ hcPoint j)
  simp [cyclicAffineHash, cyclicHashModeCode,
    MME.StothersFourth.Phi233.cyclicHashModeCode, cyclicModeWord,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    Fin.sum_univ_succ]
  push_cast at ha hb hc ⊢
  have hbNeg :
      (∑ j, (-2 : ZMod p) * (2 * ((y.2.1.1.1 0 j).val : ZMod p)) * w 1 j) =
        -∑ j, 2 * 2 * ((y.2.1.1.1 0 j).val : ZMod p) * w 1 j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ ↦ by ring)
  have hcNeg :
      (∑ j, (-2 : ZMod p) * (2 * ((x.2.2.1.1 1 j).val : ZMod p)) * w 2 j) =
        -∑ j, 2 * 2 * ((x.2.2.1.1 1 j).val : ZMod p) * w 2 j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ ↦ by ring)
  rw [hbNeg] at hb
  rw [hcNeg] at hc
  linear_combination (norm := ring_nf) ha + hb + hc
