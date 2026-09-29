-- Prove2me | solution 1 for flt5_pid_fifth_root_of_norm
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:52:34.902547+00:00
-- url     : https://prove2.me/submissions/5caa62c5-89c3-4db4-825d-d259929c42fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_ufd_coprime_conj_fifth_pow

-- Sketch: flt5_pid_fifth_root_of_norm
-- In a PID ZZ5, given β with N(β)=s^5 and β coprime to all its Galois conjugates,
-- find unit u and d with β = u * d^5.
--
-- Strategy (Kummer ideal unique factorization):
-- In a PID (=UFD), write β = ∏ pᵢ^aᵢ (prime factorization).
-- For each prime p | β, since β ⊥ σ(β) for each σ≠id, p does not divide any σ(β).
-- The product β₁ * β₂ * β₃ * β₄ = N(β) = s^5 is an integer fifth power.
-- Since p | β₁ but p ∤ β₂, β₃, β₄, we get p^(5*a₁) | s^5, hence a₁ ≡ 0 mod 5.
-- So β = u * d^5 for some unit u.
-- Delegate to flt5_ufd_coprime_conj_fifth_pow for the UFD argument.

noncomputable section

abbrev ZZ5pf := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5pf := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5pf :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5pf :=
  IsCyclotomicExtension.numberField {5} ℚ CK5pf

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution
    (hPID : IsPrincipalIdealRing ZZ5pf)
    (β : ZZ5pf) (s : ℤ) (hβ : Algebra.norm ℤ β = s ^ 5)
    (hcop : ∀ σ : CK5pf ≃ₐ[ℚ] CK5pf, σ ≠ AlgEquiv.refl →
        IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β)) :
    ∃ (u : ZZ5pfˣ) (d : ZZ5pf), β = (u : ZZ5pf) * d ^ 5 :=
  flt5_ufd_coprime_conj_fifth_pow hPID β s hβ hcop

end
