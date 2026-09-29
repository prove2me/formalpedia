-- Prove2me | solution 1 for mme_dwz_square_equation25_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T17:53:18.237649+00:00
-- url     : https://prove2.me/submissions/9b21812b-6df2-48bd-9294-7324a6854317

import Theorems.Thm_mme_dwz_square_equation25_repaired_family_raw_sqrt_loss
import Theorems.Thm_mme_dwz_square_rate_power_eq_retained_mul_component_product

open MME BigOperators Filter
open MME.DWZSquare

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((sixSymmetrization
              (TensorObj.kron (CWObj K 6) (CWObj K 6))).kronPow
                (MME.DWZTable2Counts.scale * m)) ∧
          ((squareRate tau) ^ (6 : ℕ)) ^
                (MME.DWZTable2Counts.scale * m) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C, hC, hraw⟩ :=
    mme_dwz_square_equation25_repaired_family_raw_sqrt_loss
      (K := K) tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hraw] with m hm
  obtain ⟨k, a, b, c, hrestrict, hbound⟩ := hm
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  let L : ℕ := MME.DWZTable2Counts.scale * m
  have hpow :
      ((squareRate tau) ^ (6 : ℕ)) ^ L =
        ((squareRate tau) ^ L) ^ (6 : ℕ) := by
    calc
      ((squareRate tau) ^ (6 : ℕ)) ^ L =
          (squareRate tau) ^ (6 * L) :=
        (pow_mul (squareRate tau) 6 L).symm
      _ = (squareRate tau) ^ (L * 6) := by rw [Nat.mul_comm]
      _ = ((squareRate tau) ^ L) ^ (6 : ℕ) :=
        pow_mul (squareRate tau) L 6
  rw [show MME.DWZTable2Counts.scale * m = L from rfl, hpow,
    mme_dwz_square_rate_power_eq_retained_mul_component_product tau m]
  exact hbound
