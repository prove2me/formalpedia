-- Prove2me | solution 1 for mme_CW_q6_paired_oriented_cross_fiber_projection_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T00:29:42.399539+00:00
-- url     : https://prove2.me/submissions/b26044d0-c641-4d07-b6f4-3fa6a6f4c9f5

import Theorems.Thm_mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
import Mathlib.Tactic.FinCases

/-!
The two-entry address family from the accepted common-halving counterexample
has a nonzero mixed tensor projection across distinct outer fibers. The
finite family below reproduces that accepted construction; the nonvanishing
conclusion uses the exact tensor-support equivalence.
-/

open MME MME.PairedOrientedPackaging

universe u
set_option autoImplicit false

namespace MME.PairedProjectionCounterexample

def raw (a : Fin 2) : CWQ6CoupledAddress 2 :=
  if a = 0 then
    ![![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 2, 2]]
  else
    ![![0, 1, 1, 0], ![1, 0, 1, 0], ![2, 2, 1, 0]]

def address (a : Fin 2) : CWQ6ExactCoupledAddress 2 1 1 :=
  ⟨raw a, by
    fin_cases a <;>
      simp only [CWQ6CoupledCoordinatewiseSupported, cwQ6CoupledMarginalMultiplicity, raw] <;>
      decide⟩

def family : CWQ6PrimaryHashFamily 2 1 1 2 1 where
  hHpos := by decide
  entry p := address p.1
  xInjective := by
    change Function.Injective (fun p : Fin 2 × Fin 1 ↦ raw p.1 0)
    decide
  yInjective := by
    change Function.Injective (fun p : Fin 2 × Fin 1 ↦ raw p.1 1)
    decide
  zSameFiber := by intros; rfl
  zSeparatesFibers := by
    change ∀ (a b : Fin 2) (_ _ : Fin 1), raw a 2 = raw b 2 → a = b
    decide
  induced := by
    change ∀ p q r : Fin 2 × Fin 1,
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress (raw p.1) (raw q.1) (raw r.1)) →
      p = q ∧ p.1 = r.1
    unfold CWQ6CoupledCoordinatewiseSupported cwQ6CoupledMixedAddress
    decide

def halving : family.CommonBalancedXYHalving where
  half := 1
  even_length := by decide
  position := finSumFinEquiv
  first_x := by
    change ∀ (p : Fin 2 × Fin 1) (grade : Fin 3),
      Fintype.card {j : Fin 2 // raw p.1 0 (finSumFinEquiv (Sum.inl j)) = grade} =
        if grade = 0 then 1 else if grade = 1 then 1 else 0
    decide
  second_y := by
    change ∀ (p : Fin 2 × Fin 1) (grade : Fin 3),
      Fintype.card {j : Fin 2 // raw p.1 1 (finSumFinEquiv (Sum.inr j)) = grade} =
        if grade = 0 then 1 else if grade = 1 then 1 else 0
    decide

end MME.PairedProjectionCounterexample

open MME.PairedProjectionCounterexample

/-- The literal paired projections can retain a cross term whose third entry
belongs to another outer fiber, despite a common balanced halving. -/
theorem solution
    {K : Type u} [Field K] :
    ∃ family : CWQ6PrimaryHashFamily 2 1 1 2 1,
      ∃ halving : family.CommonBalancedXYHalving,
        ∃ p q : Fin 2 × Fin 1, p.1 ≠ q.1 ∧
          PiTensorProduct.map
            (fun i => componentProj (K := K) family halving (![p, p, q] i) i)
            (TensorObj.kron
              ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
                (coupledObj K 6)).kronPow 2)
              ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow 2)).t ≠ 0 := by
  refine ⟨family, halving, (0, 0), (1, 0), by decide, ?_⟩
  apply (mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
    family halving ![(0, 0), (0, 0), (1, 0)]).mpr
  unfold CWQ6PrimaryHashFamily.PairedCyclicSupported CWQ6CoupledLocalSupported
  decide
