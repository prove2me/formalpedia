-- Prove2me | solution 2 for flt5_zz5_beta_fifth_power
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T17:14:59.642053+00:00
-- url     : https://prove2.me/submissions/98308192-bbc1-4b97-8dbd-b3e245ebe965
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_beta_coprime_conj
import Theorems.Thm_flt5_pid_fifth_root_of_norm

-- Sketch: flt5_zz5_beta_fifth_power
-- Goal: Given β:ZZ5 with N_ℤ(β)=s^5 and hPID (ZZ5 is PID), show β = u*d^5.
--
-- Strategy (Kummer PID unique factorization in ZZ5):
-- 1. Child flt5_beta_coprime_conj: β is coprime to each of its Galois conjugates.
--    For each non-trivial σ ∈ Gal(CK5/ℚ), IsCoprime β ((mapAlgEquiv σ) β) in ZZ5.
-- 2. Child flt5_pid_fifth_root_of_norm: In a PID, if β is coprime to all conjugates
--    and N(β) = s^5, then β = u * d^5 (by UFD factorization: each prime appears with
--    multiplicity ≡ 0 mod 5 in the factorization of β).

noncomputable section

abbrev ZZ5bv2 := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5bv2 := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5bv2 :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5bv2 :=
  IsCyclotomicExtension.numberField {5} ℚ CK5bv2

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (β : ZZ5bv2) (hβ : Algebra.norm ℤ β = s ^ 5)
    (hPID : IsPrincipalIdealRing ZZ5bv2) :
    ∃ (u : ZZ5bv2ˣ) (d : ZZ5bv2), β = (u : ZZ5bv2) * d ^ 5 := by
  -- Step 1: β is coprime to each Galois conjugate in ZZ5
  have hcop : ∀ σ : CK5bv2 ≃ₐ[ℚ] CK5bv2, σ ≠ AlgEquiv.refl →
      IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) :=
    flt5_beta_coprime_conj a b s h_cop β hβ hPID
  -- Step 2: UFD/PID argument: coprime to all conjugates + N=s^5 → β = u * d^5
  exact flt5_pid_fifth_root_of_norm hPID β s hβ hcop

end
