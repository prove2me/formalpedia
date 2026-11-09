-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_odd_trace_sub
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:11:19.209562+00:00
-- url     : https://prove2.me/submissions/8049a136-0deb-4381-a5b5-4d2e176be78b

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_source_target_eq_translationTriple
import Theorems.Thm_Couret_CayleyDoublet_abelianDoubletMatrix_sq_orderThree
import Theorems.Thm_Couret_CayleyDoublet_abelian_halfTurn_return_pair
import Theorems.Thm_Couret_CayleyDoublet_abelian_mem_zmultiples_halfTurn_iff
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_addOrderOf_three_iff
import Theorems.Thm_Couret_CayleySpectral_two_colour_common_sq_mul_sub
import Definitions.Def_Couret_CayleyTwoColourAbelian_32e780a833c0

/-!
COU-20 — finite directed spectral bridge (17 October 2026).

This file connects finite-support convolution to the actual rational adjacency
matrices, proves cospectrality for a supplied additive parity and for the
already certified nongeneration branch, and proves exact odd-power and trace
difference formulas. Translation sums are identified with Finset adjacency
only after distinctness has been derived from the exact quotient order.

The construction of parity from quotient cardinality and the full spectral
classification are not asserted by these conditional spectral corollaries.
No undirected-graph extension, independent human review, release or priority
claim is made here. The preceding isomorphism dichotomy is imported unchanged.
-/

set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Couret.CayleySpectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

















end Couret.CayleySpectral
namespace Couret.CayleySpectral
/-! An exact odd-power identity, valid in every unital associative ring. -/

theorem odd_pow_sub_of_sq_eq
    {R : Type*} [Ring R] (x y c : R)
    (hsq : x ^ 2 = y ^ 2)
    (heigen : x ^ 2 * (x - y) = c * (x - y)) (n : ℕ) :
    x ^ (2 * n + 1) - y ^ (2 * n + 1) = c ^ n * (x - y) := by
  have hy : Commute y (x ^ 2) := by
    rw [hsq]
    exact Commute.self_pow y 2
  have hcomm : Commute (x - y) (x ^ 2) :=
    (Commute.self_pow x 2).sub_left hy
  have hsemi : SemiconjBy (x - y) (x ^ 2) c := hcomm.eq.trans heigen
  calc
    x ^ (2 * n + 1) - y ^ (2 * n + 1) = (x - y) * (x ^ 2) ^ n := by
      rw [pow_succ', pow_succ', pow_mul, pow_mul, ← hsq, sub_mul]
    _ = c ^ n * (x - y) := hsemi.pow_right n


theorem two_colour_common_sq
    {R : Type*} [Ring R] (u v : R)
    (hu : u ^ 2 = 2 * v) (hv : v ^ 2 = 2 * u) :
    (1 + u) ^ 2 = (1 + v) ^ 2 := by
  have hu' : u * u = 2 * v := by simpa only [sq] using hu
  have hv' : v * v = 2 * u := by simpa only [sq] using hv
  noncomm_ring [hu', hv']



theorem two_colour_odd_pow_sub
    {R : Type*} [Ring R] (u v : R)
    (huv : Commute u v)
    (hu : u ^ 2 = 2 * v) (hv : v ^ 2 = 2 * u) (n : ℕ) :
    (1 + u) ^ (2 * n + 1) - (1 + v) ^ (2 * n + 1) =
      (-3) ^ n * (u - v) := by
  have h := odd_pow_sub_of_sq_eq (1 + u) (1 + v) (-3)
    (two_colour_common_sq u v hu hv)
    (two_colour_common_sq_mul_sub u v huv hu hv) n
  simpa only [add_sub_add_left_eq_sub] using h






theorem two_colour_mul_odd_pow_sub
    {R : Type*} [Ring R] (t u v : R)
    (htu : Commute t u) (htv : Commute t v) (huv : Commute u v)
    (hu : u ^ 2 = 2 * v) (hv : v ^ 2 = 2 * u) (n : ℕ) :
    (t * (1 + u)) ^ (2 * n + 1) - (t * (1 + v)) ^ (2 * n + 1) =
      t ^ (2 * n + 1) * ((-3) ^ n * (u - v)) := by
  rw [((Commute.one_right t).add_right htu).mul_pow,
    ((Commute.one_right t).add_right htv).mul_pow,
    ← mul_sub, two_colour_odd_pow_sub u v huv hu hv]


theorem two_colour_mul_odd_pow_sub_scalar_first
    {R : Type*} [Ring R] (t u v : R)
    (htu : Commute t u) (htv : Commute t v) (huv : Commute u v)
    (hu : u ^ 2 = 2 * v) (hv : v ^ 2 = 2 * u) (n : ℕ) :
    (t * (1 + u)) ^ (2 * n + 1) - (t * (1 + v)) ^ (2 * n + 1) =
      (-3) ^ n * t ^ (2 * n + 1) * (u - v) := by
  rw [two_colour_mul_odd_pow_sub t u v htu htv huv hu hv,
    ← mul_assoc,
    (((Commute.ofNat_right t 3).neg_right).pow_pow (2 * n + 1) n).eq]



end Couret.CayleySpectral

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





theorem abelianTranslationMatrix_mul (s t : G) :
    abelianTranslationMatrix s * abelianTranslationMatrix t =
      abelianTranslationMatrix (s + t) := by
  ext x y
  simp only [abelianTranslationMatrix, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
  simp [add_assoc]

theorem abelianTranslationMatrix_zero :
    abelianTranslationMatrix (0 : G) = 1 := by
  ext x y
  simp [abelianTranslationMatrix, Matrix.one_apply, eq_comm]

theorem abelianTranslationMatrix_commute (s t : G) :
    Commute (abelianTranslationMatrix s) (abelianTranslationMatrix t) := by
  show abelianTranslationMatrix s * abelianTranslationMatrix t =
    abelianTranslationMatrix t * abelianTranslationMatrix s
  simp [abelianTranslationMatrix_mul, add_comm]











end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]






omit [DecidableEq G] [Fintype G] in
theorem abelian_neg_three_mem_halfTurn (d h : G)
    (hhalf : h + h = 0)
    (hthree : (d + d) + d = 0 ∨ (d + d) + d = h) :
    ((-d) + (-d)) + (-d) = 0 ∨ ((-d) + (-d)) + (-d) = h := by
  have hn : -h = h := neg_eq_iff_add_eq_zero.mpr hhalf
  have he : ((-d) + (-d)) + (-d) = -((d + d) + d) := by abel
  rcases hthree with hthree | hthree
  · exact Or.inl (by rw [he, hthree, neg_zero])
  · exact Or.inr (by rw [he, hthree, hn])

theorem abelianDoubletMatrix_neg_sq_orderThree (d h : G)
    (hhalf : h + h = 0)
    (hthree : (d + d) + d = 0 ∨ (d + d) + d = h) :
    abelianDoubletMatrix (-d) h ^ 2 = 2 * abelianDoubletMatrix d h := by
  simpa only [neg_neg] using abelianDoubletMatrix_sq_orderThree (-d) h hhalf
    (abelian_neg_three_mem_halfTurn d h hhalf hthree)

theorem abelianTranslationMatrix_commute_doublet (a d h : G) :
    Commute (abelianTranslationMatrix a) (abelianDoubletMatrix d h) :=
  (abelianTranslationMatrix_commute a d).add_right
    (abelianTranslationMatrix_commute a (d + h))

theorem abelianDoubletMatrix_commute (d e h : G) :
    Commute (abelianDoubletMatrix d h) (abelianDoubletMatrix e h) :=
  (abelianTranslationMatrix_commute_doublet d e h).add_left
    (abelianTranslationMatrix_commute_doublet (d + h) e h)

theorem abelianTranslationMatrix_pow (a : G) (n : ℕ) :
    abelianTranslationMatrix a ^ n = abelianTranslationMatrix (n • a) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, abelianTranslationMatrix_zero]
  | succ n ih => rw [pow_succ, ih, abelianTranslationMatrix_mul, succ_nsmul]



theorem abelianTranslationTriple_eq_mul (a d h : G) :
    abelianTranslationTriple a d h =
      abelianTranslationMatrix a * (1 + abelianDoubletMatrix d h) := by
  simp [abelianTranslationTriple, abelianDoubletMatrix, mul_add,
    abelianTranslationMatrix_mul, add_assoc]



theorem abelianTranslationTriple_odd_pow_sub (a d h : G)
    (hhalf : h + h = 0)
    (hthree : (d + d) + d = 0 ∨ (d + d) + d = h) (n : ℕ) :
    abelianTranslationTriple a d h ^ (2 * n + 1) -
      abelianTranslationTriple a (-d) h ^ (2 * n + 1) =
        (-3) ^ n * abelianTranslationMatrix ((2 * n + 1) • a) *
          (abelianDoubletMatrix d h - abelianDoubletMatrix (-d) h) := by
  rw [abelianTranslationTriple_eq_mul, abelianTranslationTriple_eq_mul]
  rw [← abelianTranslationMatrix_pow]
  exact two_colour_mul_odd_pow_sub_scalar_first _ _ _
    (abelianTranslationMatrix_commute_doublet a d h)
    (abelianTranslationMatrix_commute_doublet a (-d) h)
    (abelianDoubletMatrix_commute d (-d) h)
    (abelianDoubletMatrix_sq_orderThree d h hhalf hthree)
    (abelianDoubletMatrix_neg_sq_orderThree d h hhalf hthree) n


theorem abelianTranslationMatrix_trace (t : G) :
    Matrix.trace (abelianTranslationMatrix t) =
      if t = 0 then (Fintype.card G : ℚ) else 0 := by
  have he (x : G) : x = x + t ↔ t = 0 := by
    constructor
    · intro hx
      have hz : (0 : G) = t := add_left_cancel (by simpa only [add_zero] using hx)
      exact hz.symm
    · rintro rfl
      exact (add_zero x).symm
  simp [Matrix.trace, Matrix.diag, abelianTranslationMatrix, he]

omit [AddCommGroup G] in
theorem abelianMatrix_intCast_mul (z : ℤ) (M : Matrix G G ℚ) :
    (z : Matrix G G ℚ) * M = (z : ℚ) • M := by
  rw [← Matrix.diagonal_intCast, ← Matrix.smul_eq_diagonal_mul]

omit [AddCommGroup G] in
theorem abelianMatrix_negThree_pow_mul (n : ℕ) (M : Matrix G G ℚ) :
    (-3 : Matrix G G ℚ) ^ n * M = (-3 : ℚ) ^ n • M := by
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_ofNat] using
    abelianMatrix_intCast_mul ((-3 : ℤ) ^ n) M

theorem abelianTranslationTriple_odd_trace_sub (a d h : G)
    (hhalf : h + h = 0)
    (hthree : (d + d) + d = 0 ∨ (d + d) + d = h) (n : ℕ) :
    Matrix.trace (abelianTranslationTriple a d h ^ (2 * n + 1)) -
      Matrix.trace (abelianTranslationTriple a (-d) h ^ (2 * n + 1)) =
      (-3 : ℚ) ^ n *
        ((if (2 * n + 1) • a + d = 0 then (Fintype.card G : ℚ) else 0) +
          (if (2 * n + 1) • a + (d + h) = 0 then (Fintype.card G : ℚ) else 0) -
          ((if (2 * n + 1) • a + (-d) = 0 then (Fintype.card G : ℚ) else 0) +
          (if (2 * n + 1) • a + (-d + h) = 0 then (Fintype.card G : ℚ) else 0))) := by
  rw [← Matrix.trace_sub, abelianTranslationTriple_odd_pow_sub a d h hhalf hthree n,
    mul_assoc, abelianMatrix_negThree_pow_mul, Matrix.trace_smul]
  simp only [abelianDoubletMatrix, mul_sub, mul_add, abelianTranslationMatrix_mul,
    Matrix.trace_sub, Matrix.trace_add, abelianTranslationMatrix_trace, smul_eq_mul]




theorem abelianTranslationTriple_odd_trace_sub_halfTurn (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hthree : (d + d) + d = 0 ∨ (d + d) + d = h) (n : ℕ) :
    Matrix.trace (abelianTranslationTriple a d h ^ (2 * n + 1)) -
      Matrix.trace (abelianTranslationTriple a (-d) h ^ (2 * n + 1)) =
      (-3 : ℚ) ^ n *
        ((if (2 * n + 1) • a + d = 0 ∨ (2 * n + 1) • a + d = h
            then (Fintype.card G : ℚ) else 0) -
          (if (2 * n + 1) • a + (-d) = 0 ∨ (2 * n + 1) • a + (-d) = h
            then (Fintype.card G : ℚ) else 0)) := by
  rw [abelianTranslationTriple_odd_trace_sub a d h hhalf hthree n]
  rw [← add_assoc ((2 * n + 1) • a) d h,
    ← add_assoc ((2 * n + 1) • a) (-d) h,
    abelian_halfTurn_return_pair _ h _ hhalf hne,
    abelian_halfTurn_return_pair _ h _ hhalf hne]



end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]























/-- Exact odd-trace difference in terms of return to the half-turn subgroup. -/
theorem p2m_local_abelianThree_odd_trace_sub
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) (n : ℕ) :
    Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ (2 * n + 1)) -
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ (2 * n + 1)) =
      (-3 : ℚ) ^ n *
        ((if (2 * n + 1) • a + d ∈ AddSubgroup.zmultiples h
          then (Fintype.card G : ℚ) else 0) -
         (if (2 * n + 1) • a - d ∈ AddSubgroup.zmultiples h
          then (Fintype.card G : ℚ) else 0)) := by
  obtain ⟨hthree, _, _⟩ :=
    (abelian_quotient_addOrderOf_three_iff d h hhalf).mp horder
  obtain ⟨hS, hT⟩ :=
    abelianCayleyMatrix_source_target_eq_translationTriple a d h hhalf hne horder
  rw [hS, hT]
  simp only [abelian_mem_zmultiples_halfTurn_iff h ((2 * n + 1) • a + d) hhalf,
    abelian_mem_zmultiples_halfTurn_iff h ((2 * n + 1) • a - d) hhalf]
  simpa only [sub_eq_add_neg] using
    abelianTranslationTriple_odd_trace_sub_halfTurn a d h hhalf hne hthree n



end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a d h : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        h h)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G h
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Eq.{1} Nat
          (@addOrderOf.{p2m_u_0}
            (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
            (@SubNegMonoid.toAddMonoid.{p2m_u_0}
              (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
              (@AddGroup.toSubNegMonoid.{p2m_u_0}
                (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                (@QuotientAddGroup.Quotient.addGroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                  (@AddSubgroup.normal_of_isAddCommutative.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@AddCommMagma.to_isCommutative.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
            (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) d))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        ∀ (n : Nat),
          @Eq.{1} Rat
            (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
              (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                  (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                  (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                    (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                      (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                        (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                  (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                  (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                    (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                      (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                        (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
              (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                (@Neg.neg.{0} Rat Rat.instNeg (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))) n)
              (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                (@ite.{1} Rat
                  (@Membership.mem.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                      (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat G G
                        (@instHSMul.{0, p2m_u_0} Nat G
                          (@AddMonoid.toNSMul.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      d))
                  (@AddSubgroup.decidableMemZMultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat G G
                        (@instHSMul.{0, p2m_u_0} Nat G
                          (@AddMonoid.toNSMul.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      d))
                  (@Nat.cast.{0} Rat Rat.instNatCast (@Fintype.card.{p2m_u_0} G inst_2))
                  (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
                (@ite.{1} Rat
                  (@Membership.mem.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                      (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                    (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHSub.{p2m_u_0} G
                        (@SubNegMonoid.toSub.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                      (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat G G
                        (@instHSMul.{0, p2m_u_0} Nat G
                          (@AddMonoid.toNSMul.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      d))
                  (@AddSubgroup.decidableMemZMultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h
                    (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHSub.{p2m_u_0} G
                        (@SubNegMonoid.toSub.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                      (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat G G
                        (@instHSMul.{0, p2m_u_0} Nat G
                          (@AddMonoid.toNSMul.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      d))
                  (@Nat.cast.{0} Rat Rat.instNatCast (@Fintype.card.{p2m_u_0} G inst_2))
                  (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_odd_trace_sub

