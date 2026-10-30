-- Prove2me | solution 1 for AnalyticCombinatorics.atom_lcyc_counts_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T21:23:11.194096+00:00
-- url     : https://prove2.me/submissions/c2f3209b-78d1-4d0a-9873-597de495e52a

import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Alignments
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.1 — Combinatorial classes and ordinary generating functions

A faithful encoding of Flajolet & Sedgewick, *Analytic Combinatorics*, Part A,
Chapter I, §I.1. A combinatorial class is a set of objects equipped with a size
function such that only finitely many objects have any given size. We encode it
as a graded family of finite types `Obj : ℕ → Type`, where `Obj n` is the set of
objects of size `n`. Its counting sequence is `Aₙ = #(Obj n)`, and its *ordinary
generating function* (OGF) is `A(z) = ∑ₙ Aₙ zⁿ`, here a formal power series over
`ℚ`.

This file defines the OGF, the `CombClass` structure, and the three primitive
classes (empty `∅`, neutral `ε`, atom `Z`) with their counting sequences and
generating functions `ε(z) = 1`, `Z(z) = z`. The admissible constructions (sum,
product, sequence) and their transfer theorems live in sibling files.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

attribute [instance] CombClass.finObj

/-! ### Primitive classes

We encode the primitive classes with `Obj n := Fin (· n)` so that the `Fintype`
instance is uniform; their entire content is their counting sequence. -/

@[simp] lemma CombClass.counts_neutral (n : ℕ) :
    CombClass.neutral.counts n = if n = 0 then 1 else 0 :=
  Fintype.card_fin _

@[simp] lemma CombClass.counts_atom (n : ℕ) :
    CombClass.atom.counts n = if n = 1 then 1 else 0 :=
  Fintype.card_fin _

end AnalyticCombinatorics.Ch1

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
# Ch2 §II.1 — Labelled powers

Flajolet & Sedgewick, Part A, Chapter II. Iterating the labelled product gives the
`k`-th labelled power `C^{⋆k}`, with EGF `C(z)^k` (an immediate induction from the
labelled product rule). The neutral class `ε` is the unit, with EGF `1`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The EGF of the neutral class `ε` is `1`. -/
theorem CombClass.egf_neutral : CombClass.neutral.egf = 1 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_neutral]
  rcases n with _ | m <;> simp [coeff_one]

/-- **Labelled power rule**: `(C^{⋆k})(z) = C(z)^k`. -/
@[simp] theorem CombClass.egf_lpow (C : CombClass) (k : ℕ) :
    (C.lpow k).egf = C.egf ^ k := by
  set_option backward.isDefEq.respectTransparency false in
    induction k with
    | zero => simp [CombClass.lpow, CombClass.egf_neutral]
    | succ k ih => rw [CombClass.lpow, CombClass.egf_lprod, ih, pow_succ']

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.1 — The labelled sequence construction

Flajolet & Sedgewick, Part A, Chapter II. `SEQ(C)` is the disjoint union of all
labelled powers `C^{⋆k}`. When `C₀=∅`, only powers `k ≤ n` contribute to size `n`,
and the EGF is the geometric series

  `SEQ(C)(z) = 1 / (1 - C(z))`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- Counting identity for labelled sequences: `SEQ(C)ₙ` is the finite sum of the
counts of the labelled powers contributing to size `n`. -/
lemma CombClass.counts_lseq (C : CombClass) (n : ℕ) :
    C.lseq.counts n = ∑ k : Fin (n + 1), (C.lpow k).counts n := by
  change Fintype.card (Σ k : Fin (n + 1), (C.lpow k).Obj n) = _
  rw [Fintype.card_sigma]
  rfl

section EGF

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatLseq

local instance instDiscRatLseq : DiscreteTopology ℚ := ⟨rfl⟩

/-- **Labelled sequence rule** (F&S Theorem II.2): if `C₀=∅`, then
`SEQ(C)(z) = 1/(1 - C(z))`, stated multiplicatively. -/
theorem CombClass.egf_lseq (C : CombClass) (hC : C.counts 0 = 0) :
    C.lseq.egf * (1 - C.egf) = 1 := by
  have h0 : constantCoeff C.egf = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf, hC]
    norm_num
  have hseq : C.lseq.egf = ∑' k : ℕ, C.egf ^ k := by
    ext n
    have hfinite :
        coeff n C.lseq.egf = ∑ k : Fin (n + 1), coeff n (C.egf ^ (k : ℕ)) := by
      rw [CombClass.coeff_egf, CombClass.counts_lseq, Nat.cast_sum, div_eq_mul_inv,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← CombClass.egf_lpow C (k : ℕ), CombClass.coeff_egf, div_eq_mul_inv]
    have htail : ∀ k : ℕ, n < k → coeff n (C.egf ^ k) = 0 := by
      intro k hk
      exact coeff_of_lt_order n
        ((ENat.coe_lt_coe.mpr hk).trans_le
          (le_order_pow_of_constantCoeff_eq_zero k h0))
    have hsumm : Summable fun k : ℕ => C.egf ^ k :=
      summable_pow_of_constantCoeff_eq_zero h0
    calc
      coeff n C.lseq.egf
          = ∑ k : Fin (n + 1), coeff n (C.egf ^ (k : ℕ)) := hfinite
      _ = ∑ k ∈ Finset.range (n + 1), coeff n (C.egf ^ k) := by
          rw [Fin.sum_univ_eq_sum_range (fun k => coeff n (C.egf ^ k)) (n + 1)]
      _ = ∑' k : ℕ, coeff n (C.egf ^ k) := by
          exact (tsum_eq_sum (s := Finset.range (n + 1)) fun k hk => by
            rw [Finset.mem_range, not_lt] at hk
            exact htail k (Nat.lt_of_succ_le hk)).symm
      _ = coeff n (∑' k : ℕ, C.egf ^ k) := by
          exact (hsumm.map_tsum (coeff n) (continuous_coeff ℚ n)).symm
  rw [hseq]
  exact tsum_pow_mul_one_sub_of_constantCoeff_eq_zero h0

end EGF
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

/-- The ODE and zero constant term characterize the labelled cycle EGF. -/
theorem CombClass.egf_lcyc_unique (C : CombClass) (hC : C.counts 0 = 0) {F : ℚ⟦X⟧}
    (hF' : d⁄dX ℚ F = d⁄dX ℚ C.egf * C.lseq.egf)
    (hF0 : constantCoeff F = 0) :
    F = C.lcyc.egf :=
  PowerSeries.derivative.ext
    (by rw [hF', CombClass.egf_lcyc_ode C hC])
    (by rw [hF0, CombClass.constantCoeff_egf_lcyc])

end AnalyticCombinatorics.Ch1

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Alignments

open AnalyticCombinatorics.Ch1

lemma coeff_cycleEGFℚ (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n cycleEGFℚ = ((n : ℚ)⁻¹) := by
  simp [cycleEGFℚ]

lemma cycleEGFℚ_constantCoeff :
    PowerSeries.constantCoeff cycleEGFℚ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_cycleEGFℚ]
  simp

lemma atom_counts_zero : CombClass.atom.counts 0 = 0 := by
  simp [CombClass.counts_atom]

theorem egf_atom : CombClass.atom.egf = (PowerSeries.X : PowerSeries ℚ) := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_atom]
  by_cases h1 : n = 1
  · subst n
    simp
  · have hcoeffX : PowerSeries.coeff (R := ℚ) n PowerSeries.X = 0 := by
      rw [PowerSeries.coeff_X]
      simp [h1]
    rw [if_neg h1, hcoeffX]
    simp

lemma atom_lseq_egf_eq_geometric :
    CombClass.atom.lseq.egf = PowerSeries.invUnitsSub (1 : ℚˣ) := by
  have hmul := CombClass.egf_lseq CombClass.atom atom_counts_zero
  rw [egf_atom] at hmul
  have h0 : PowerSeries.constantCoeff (1 - (PowerSeries.X : PowerSeries ℚ)) ≠ 0 := by
    simp
  have hseq : CombClass.atom.lseq.egf = (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one h0).2 hmul
  have hgeom :
      PowerSeries.invUnitsSub (1 : ℚˣ) = (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one h0).2 (by
    simpa only [Units.val_one] using
      (PowerSeries.invUnitsSub_mul_sub (u := (1 : ℚˣ))))
  exact hseq.trans hgeom.symm

lemma derivative_cycleEGFℚ :
    d⁄dX ℚ cycleEGFℚ = PowerSeries.invUnitsSub (1 : ℚˣ) := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_cycleEGFℚ, PowerSeries.coeff_invUnitsSub]
  simp [Nat.cast_add, Nat.cast_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]

theorem atom_lcyc_egf_eq_cycleEGFℚ :
    CombClass.atom.lcyc.egf = cycleEGFℚ := by
  have hF' :
      d⁄dX ℚ cycleEGFℚ =
        d⁄dX ℚ CombClass.atom.egf * CombClass.atom.lseq.egf := by
    set_option backward.isDefEq.respectTransparency false in
      rw [derivative_cycleEGFℚ, egf_atom, PowerSeries.derivative_X, one_mul,
        atom_lseq_egf_eq_geometric]
  have hF0 : PowerSeries.constantCoeff cycleEGFℚ = 0 :=
    cycleEGFℚ_constantCoeff
  exact (CombClass.egf_lcyc_unique CombClass.atom atom_counts_zero hF' hF0).symm

end Alignments
end Meromorphic
end Ch5
end AnalyticCombinatorics
end

/-!
# The labelled-cycle count `(n-1)!` (F&S §II.2, the CYC logarithm)

The Ch2 cycle construction `CYC` is characterized at the EGF level by the ODE
`CYC(C)' = C'·SEQ(C)` together with a zero constant term
(`CombClass.egf_lcyc_unique`).  For the atomic class `Z` this pins the EGF down to
the **logarithm** `L(z) = log(1/(1-z)) = Σ_{n≥1} zⁿ/n` (`atom_lcyc_egf_eq_cycleEGFℚ`,
with `coeff n cycleEGFℚ = 1/n`).

This file records the resulting *combinatorial* closed form — the signature CYC
fact that an `n`-element labelled set admits exactly `(n-1)!` distinct cyclic
arrangements:

  `atom.lcyc.counts n = (n-1)!`  (`n ≥ 1`).

It is the integer shadow of the analytic identity `[zⁿ] log(1/(1-z)) = 1/n`
read through `[zⁿ] EGF = counts n / n!`, since `n!/n = (n-1)!`.
-/

open PowerSeries

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

end AnalyticCombinatorics

open AnalyticCombinatorics
open PowerSeries
open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    CombClass.atom.lcyc.counts n = (n - 1).factorial := by
  -- `[zⁿ] CYC(Z).egf = counts n / n!` equals `[zⁿ] log(1/(1-z)) = 1/n`.
  have hcoeff :
      (CombClass.atom.lcyc.counts n : ℚ) / (n.factorial : ℚ) = (n : ℚ)⁻¹ := by
    rw [← CombClass.coeff_egf, atom_lcyc_egf_eq_cycleEGFℚ, coeff_cycleEGFℚ]
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac0 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  -- `n! = n · (n-1)!`.
  have hfact : (n.factorial : ℚ) = (n : ℚ) * ((n - 1).factorial : ℚ) := by
    have hnat : n.factorial = n * (n - 1).factorial := by
      cases n with
      | zero => exact absurd hn (by norm_num)
      | succ m => rw [Nat.factorial_succ, Nat.succ_sub_one]
    exact_mod_cast hnat
  -- Solve `counts/n! = 1/n` for `counts`, then cast back to `ℕ`.
  rw [div_eq_iff hfac0] at hcoeff
  have key : (CombClass.atom.lcyc.counts n : ℚ) = ((n - 1).factorial : ℚ) := by
    rw [hcoeff, hfact, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  exact_mod_cast key
