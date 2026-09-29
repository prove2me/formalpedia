-- Prove2me | solution 2 for flt5_zz5_lambda_dvd_five
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-13T13:30:34.208359+00:00
-- url     : https://prove2.me/submissions/3f0df8b1-1c5e-4717-bdbf-d91e7ae6e0ea

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic

-- (1 - ζ) | 5 in ZZ5 via: (1-ζ)*(ζ³+2ζ²+3ζ+4) = 5
-- Uses Φ₅(ζ)=0: (ζ-1)(ζ⁴+ζ³+ζ²+ζ+1) = ζ⁵-1 = 0, ζ≠1 → ζ⁴+ζ³+ζ²+ζ+1 = 0

noncomputable section

abbrev ZZ5ld := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5ld := CyclotomicField 5 ℚ

instance inst1ld : IsCyclotomicExtension {5} ℚ CK5ld :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance inst2ld : NumberField CK5ld :=
  IsCyclotomicExtension.numberField {5} ℚ CK5ld

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (ζ : ZZ5ld)
    (hζ : IsPrimitiveRoot (ζ : CK5ld) 5) :
    (1 - ζ) ∣ (5 : ZZ5ld) := by
  suffices h : (1 - ζ) * (ζ ^ 3 + 2 * ζ ^ 2 + 3 * ζ + 4) = 5 from ⟨_, h.symm⟩
  -- Φ₅(ζ) = 0 in CK5ld
  have hphi : (ζ : CK5ld) ^ 4 + (ζ : CK5ld) ^ 3 + (ζ : CK5ld) ^ 2 + (ζ : CK5ld) + 1 = 0 := by
    have hfact : ((ζ : CK5ld) - 1) *
        ((ζ : CK5ld) ^ 4 + (ζ : CK5ld) ^ 3 + (ζ : CK5ld) ^ 2 + (ζ : CK5ld) + 1) = 0 :=
      calc ((ζ : CK5ld) - 1) * ((ζ : CK5ld) ^ 4 + (ζ : CK5ld) ^ 3 +
              (ζ : CK5ld) ^ 2 + (ζ : CK5ld) + 1)
          = (ζ : CK5ld) ^ 5 - 1 := by ring
        _ = 0 := by rw [hζ.pow_eq_one]; ring
    rcases mul_eq_zero.mp hfact with h | h
    · exact absurd (sub_eq_zero.mp h) (hζ.ne_one (by norm_num))
    · exact h
  -- Equality in ZZ5ld follows from equality after coercion to CK5ld
  -- (coercion is injective via Subtype.val_injective)
  have hinj : Function.Injective (algebraMap ZZ5ld CK5ld) := by
    intro a b hab
    exact Subtype.val_inj.mp hab
  apply hinj
  simp only [map_mul, map_sub, map_one, map_pow, map_add, map_ofNat]
  linear_combination -hphi

end
