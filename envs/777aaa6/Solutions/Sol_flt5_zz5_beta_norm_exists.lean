-- Prove2me | solution 1 for flt5_zz5_beta_norm_exists
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T08:55:20.649571+00:00
-- url     : https://prove2.me/submissions/e7073e50-ac75-478b-9756-a63ad456aab6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_zz5_beta_norm_exists
import Theorems.Thm_flt5_zz5_lam_dvd_numerator
import Theorems.Thm_flt5_zz5_norm_quotient_is_power

-- Sketch for flt5_zz5_beta_norm_exists
-- Strategy:
--   Child 1 (flt5_zz5_lam_dvd_numerator): Show λ=(1-ζ) | (a+ζb) in ZZ5 when 5|(a+b).
--     Key: ζ≡1 (mod λ), so a+ζb ≡ a+b ≡ 0 (mod λ) since λ|(5)|(a+b).
--   Child 2 (flt5_zz5_norm_quotient_is_power): Given (a+ζb)=(1-ζ)*γ,
--     use N(a+ζb)=Phi(a,b)=5*s^5 and N(λ)=5 to get N(γ)=s^5.

noncomputable section

abbrev ZZ5bn := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)

instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField (CyclotomicField 5 ℚ) :=
  IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (h5sum : (5 : ℤ) ∣ a + b)
    (hPID : IsPrincipalIdealRing ZZ5bn) :
    ∃ β : ZZ5bn, Algebra.norm ℤ β = s ^ 5 := by
  have hζ_spec : IsPrimitiveRoot (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ)) 5 :=
    IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)
  let ζ : ZZ5bn := ⟨IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ),
    hζ_spec.isIntegral (by norm_num)⟩
  have hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5 := hζ_spec
  obtain ⟨γ, hγ⟩ := flt5_zz5_lam_dvd_numerator a b h5sum ζ hζ
  exact ⟨γ, flt5_zz5_norm_quotient_is_power a b s h_cop hPhi ζ hζ γ hγ hPID⟩

end
