-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.egf_lcyc_unique
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:00:54.456575+00:00
-- url     : https://prove2.me/submissions/c456cfca-364b-4465-a68e-4786ff3f38aa

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Substitution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_egfSeq (a : ℕ → ℕ) (n : ℕ) :
    coeff n (egfSeq a) = (a n : ℚ) / (n.factorial : ℚ) := by
  rw [egfSeq, coeff_mk]

@[simp] lemma CombClass.coeff_egf (C : CombClass) (n : ℕ) :
    coeff n C.egf = (C.counts n : ℚ) / (n.factorial : ℚ) := by
  rw [CombClass.egf, coeff_egfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.1 — The labelled product

Flajolet & Sedgewick, Part A, Chapter II, the labelled (partitional) product, the
defining construction of the EGF framework. To form `A ⋆ B` on `n` labels, one
chooses which `k` of the labels go to the `A`-component (a `k`-subset) and puts an
`A`-structure on them and a `B`-structure on the remaining `n-k`. Hence

  `(A ⋆ B)ₙ = ∑_{k} C(n,k) · Aₖ · B_{n-k}`   (binomial convolution),

and therefore the EGFs multiply:

  **`(A ⋆ B)(z) = A(z) · B(z)`**   (F&S Theorem II.1).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Counting sequences convolve binomially: `(A ⋆ B)ₙ = ∑_k C(n,k)·Aₖ·B_{n-k}`. -/
@[simp] lemma CombClass.counts_lprod (A B : CombClass) (n : ℕ) :
    (A.lprod B).counts n
      = ∑ k : Fin (n + 1), n.choose k * A.counts k * B.counts (n - k) := by
  change Fintype.card
      (Σ k : Fin (n + 1), { S : Finset (Fin n) // S.card = k } × A.Obj k × B.Obj (n - k)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_finset_len, Fintype.card_fin]
  simp only [CombClass.counts]
  ring

/-- **Labelled product rule** (F&S Theorem II.1): `(A ⋆ B)(z) = A(z)·B(z)`. -/
theorem CombClass.egf_lprod (A B : CombClass) :
    (A.lprod B).egf = A.egf * B.egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_lprod, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Fin.sum_univ_eq_sum_range
      (fun k => n.choose k * A.counts k * B.counts (n - k)) (n + 1),
    Nat.cast_sum, div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero n), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hk' : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk' : ((n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  rw [CombClass.coeff_egf, CombClass.coeff_egf]
  field_simp
  rw [← Nat.choose_mul_factorial_mul_factorial hk]
  push_cast
  ring

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled set ODE

This file contains the coefficient-level machinery for the differential equation
of the labelled set construction.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The EGF of the derivative class is the formal derivative of the EGF. -/
theorem CombClass.egf_deriv (C : CombClass) :
    C.deriv.egf = d⁄dX ℚ C.egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_deriv, coeff_derivative,
    CombClass.coeff_egf]
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hnf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [Nat.factorial_succ, hn, hnf]
  rw [Nat.factorial_succ]
  push_cast
  ring_nf

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled cycle construction

This file gives a concrete canonical-rotation model for labelled cycles.  A
nonempty labelled power represents a cycle by rotating it so that the first
block contains the largest label.  The transfer theorem is stated as the
defining differential equation

  `CYC(C)' = C' * SEQ(C)`, with zero constant term.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The pointed cycle recurrence at the EGF level. -/
theorem CombClass.egf_lcyc_deriv_lprod (C : CombClass) (hC : C.counts 0 = 0) :
    C.lcyc.deriv.egf = (C.deriv.lprod C.lseq).egf := by
  ext n
  have hcounts :
      C.lcyc.deriv.counts n = (C.deriv.lprod C.lseq).counts n := by
    exact Fintype.card_congr (lcycDerivEquivLprodLseq C hC n)
  rw [CombClass.coeff_egf, CombClass.coeff_egf, hcounts]

/-- The cycle class has zero constant term. -/
theorem CombClass.constantCoeff_egf_lcyc (C : CombClass) :
    constantCoeff C.lcyc.egf = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf]
  simp [CombClass.counts, CombClass.lcyc]

/-- The labelled cycle construction satisfies `CYC(C)' = C' * SEQ(C)`. -/
theorem CombClass.egf_lcyc_ode (C : CombClass) (hC : C.counts 0 = 0) :
    d⁄dX ℚ C.lcyc.egf = d⁄dX ℚ C.egf * C.lseq.egf := by
  calc
    d⁄dX ℚ C.lcyc.egf = C.lcyc.deriv.egf := (CombClass.egf_deriv C.lcyc).symm
    _ = (C.deriv.lprod C.lseq).egf := CombClass.egf_lcyc_deriv_lprod C hC
    _ = C.deriv.egf * C.lseq.egf := CombClass.egf_lprod C.deriv C.lseq
    _ = d⁄dX ℚ C.egf * C.lseq.egf := by rw [CombClass.egf_deriv C]

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries Finset
theorem solution (C : CombClass) (hC : C.counts 0 = 0) {F : ℚ⟦X⟧}
    (hF' : d⁄dX ℚ F = d⁄dX ℚ C.egf * C.lseq.egf)
    (hF0 : constantCoeff F = 0) :
    F = C.lcyc.egf :=
  PowerSeries.derivative.ext
    (by rw [hF', CombClass.egf_lcyc_ode C hC])
    (by rw [hF0, CombClass.constantCoeff_egf_lcyc])
