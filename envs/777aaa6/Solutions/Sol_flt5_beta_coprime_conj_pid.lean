-- Prove2me | solution 1 for flt5_beta_coprime_conj_pid
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:52:34.674608+00:00
-- url     : https://prove2.me/submissions/5faed887-9d48-4819-b15c-43028d3b8023
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_kummer_coprimeness_pid

-- Sketch: flt5_beta_coprime_conj_pid
-- Given a,b,s with gcd(a,b)=1, β:ZZ5 with N(β)=s^5, ZZ5 is a PID,
-- prove β is coprime to each nontrivial Galois conjugate σ(β).
--
-- Strategy (Kummer 1825):
-- β - σ(β) = b*(ζ^1 - ζ^k) = b * (unit in ZZ5) * λ for k≢0 mod 5.
-- Any common divisor d | β and d | σ(β) divides β - σ(β) = b*unit*λ.
-- Case 1: d | λ. Then since N(λ)=5 and N(β)=s^5 with gcd(a,b)=1, λ cannot
--   divide all four β conjugates; contradiction with d | both β and σ(β).
-- Case 2: d | b. Then d | N(β) = s^5 ∈ ℤ and d | N(b) = b^4, gcd conditions
--   force d to be a unit.
-- Delegate to flt5_kummer_coprimeness_pid for the complete argument.

noncomputable section

abbrev ZZ5bcjpid := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5bcjpid := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5bcjpid :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5bcjpid :=
  IsCyclotomicExtension.numberField {5} ℚ CK5bcjpid

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (β : ZZ5bcjpid) (hβ : Algebra.norm ℤ β = s ^ 5)
    (hPID : IsPrincipalIdealRing ZZ5bcjpid) :
    ∀ σ : CK5bcjpid ≃ₐ[ℚ] CK5bcjpid, σ ≠ AlgEquiv.refl →
    IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) :=
  flt5_kummer_coprimeness_pid a b s h_cop β hβ hPID

end
