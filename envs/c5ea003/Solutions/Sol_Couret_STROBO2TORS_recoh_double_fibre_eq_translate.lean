-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_double_fibre_eq_translate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:12.336168+00:00
-- url     : https://prove2.me/submissions/e43348a2-beea-46e5-9e93-7f75b73f9400

import Aesop
import Definitions.Def_Couret_RecohDecoderBounds_60ec29457baa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6

set_option autoImplicit false

/-!
Finite combinatorial bounds for the RECOH candidate decoder.

Each possible three-element edge set E contributes either no half-sum or a
coset of the actual subgroup G[2].  The general counting bound is the number
of edge sets times |G[2]|.  The numerical factor twenty is used only when
the observed square has support of cardinality at most six; this hypothesis
is proved for the ordered square of an actual three-element support.

These are cardinality statements about the finite candidate specification.
They do not by themselves assert a running-time bound for its implementation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



@[simp]
theorem recoh_mem_double_fibre (t sigma : G) :
    sigma ∈ recohDoubleFibre t ↔ sigma + sigma = t := by
  simp [recohDoubleFibre]

/-- A nonempty doubling fibre is a translate of its zero fibre, hence a
coset of `G[2]`.  The chosen base point is any solution of the half-sum. -/
theorem p2m_local_recoh_double_fibre_eq_translate (t sigma : G)
    (hsigma : sigma + sigma = t) :
    recohDoubleFibre t = translateSupport (recohDoubleFibre (0 : G)) sigma := by
  ext x
  constructor
  · intro hx
    rw [translateSupport, Finset.mem_image]
    refine ⟨x - sigma, ?_, sub_add_cancel x sigma⟩
    apply (recoh_mem_double_fibre _ _).mpr
    exact (double_eq_iff_two_torsion sigma x).mp
      (hsigma.trans ((recoh_mem_double_fibre _ _).mp hx).symm)
  · intro hx
    rw [translateSupport, Finset.mem_image] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    apply (recoh_mem_double_fibre _ _).mpr
    calc
      (u + sigma) + (u + sigma) = (sigma + sigma) + (u + u) := by abel
      _ = t := by rw [hsigma, (recoh_mem_double_fibre _ _).mp hu, add_zero]























end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (t sigma : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        sigma sigma)
      t →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.recohDoubleFibre.{p2m_u_0} G inst inst_1 inst_2 t)
      (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1
        (@Couret.STROBO2TORS.recohDoubleFibre.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
        sigma) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_double_fibre_eq_translate

