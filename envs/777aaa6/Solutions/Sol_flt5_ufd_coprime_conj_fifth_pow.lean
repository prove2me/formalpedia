-- Prove2me | solution 1 for flt5_ufd_coprime_conj_fifth_pow
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:59:44.131631+00:00
-- url     : https://prove2.me/submissions/358dc2af-77cf-4bd9-9595-1a5d5acaf2ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_ufd_fifth_power_lemma

-- Sketch: flt5_ufd_coprime_conj_fifth_pow
-- In a PID ZZ5, if β has N(β)=s^5 and β coprime to each Galois conjugate,
-- then β = u * d^5 for unit u and d : ZZ5.
-- Delegates to flt5_ufd_fifth_power_lemma which proves the UFD argument:
-- each prime p in the prime factorization of β appears with multiplicity ≡ 0 mod 5
-- (from coprimeness to conjugates and N(β) = s^5), giving β = u * d^5.

noncomputable section

abbrev ZZ5ufd := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5ufd := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5ufd :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5ufd :=
  IsCyclotomicExtension.numberField {5} ℚ CK5ufd

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution
    (hPID : IsPrincipalIdealRing ZZ5ufd)
    (β : ZZ5ufd) (s : ℤ) (hβ : Algebra.norm ℤ β = s ^ 5)
    (hcop : ∀ σ : CK5ufd ≃ₐ[ℚ] CK5ufd, σ ≠ AlgEquiv.refl →
        IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β)) :
    ∃ (u : ZZ5ufdˣ) (d : ZZ5ufd), β = (u : ZZ5ufd) * d ^ 5 :=
  flt5_ufd_fifth_power_lemma hPID β s hβ hcop

end
