-- Prove2me | solution 1 for flt5_kummer_coprimeness_pid
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:59:43.887362+00:00
-- url     : https://prove2.me/submissions/da9c423f-d715-4f78-a15b-009f85b18f80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_kummer_coprime_zz5

-- Sketch: flt5_kummer_coprimeness_pid
-- Delegates to flt5_kummer_coprime_zz5, which encapsulates the full
-- Kummer coprimeness argument in Z[ζ₅]:
-- - For σ ≠ id, β - σ(β) = b * unit * λ in ZZ5
-- - Any common divisor of β and σ(β) must be a unit
--   (using N(β)=s^5, gcd(a,b)=1, and PID structure)

noncomputable section

abbrev ZZ5kcp := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5kcp := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5kcp :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5kcp :=
  IsCyclotomicExtension.numberField {5} ℚ CK5kcp

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (β : ZZ5kcp) (hβ : Algebra.norm ℤ β = s ^ 5)
    (hPID : IsPrincipalIdealRing ZZ5kcp) :
    ∀ σ : CK5kcp ≃ₐ[ℚ] CK5kcp, σ ≠ AlgEquiv.refl →
    IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) :=
  flt5_kummer_coprime_zz5 a b s h_cop β hβ hPID

end
