-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.exp_egf_lcyc
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:00:48.875629+00:00
-- url     : https://prove2.me/submissions/551689c6-2079-4b93-b044-21e5033a5066

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.EquivFin

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
# Ch2 §II.2 — ODE machinery for the labelled set construction

Toward the labelled set transfer `SET(C)(z) = exp(C(z))` (F&S §II.2). The strategy
(differential route): `exp(C(z))` and `SET(C)(z)` both satisfy the linear ODE
`F' = C'(z)·F` with constant term `1`, and that ODE has a unique solution. This file
proves the two *general* (combinatorics-free) ingredients:

* `subst_exp_ode` — `exp(C(z)) := (exp ℚ).subst C.egf` satisfies `F' = C'·F`
  (the chain rule `derivative_subst` + `derivative_exp`).
* `ode_unique` — a power series with `H' = G·H` and `H(0) = 0` is `0`.

The remaining (combinatorial) ingredient — that `SET(C).egf` satisfies the same ODE,
via a pointing bijection on set partitions — is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- **ODE uniqueness**: a power series solving `H' = G·H` with vanishing constant term
is `0` (coefficient induction). -/
theorem ode_unique {R : Type*} [CommSemiring R] [Algebra ℚ R] {H G : R⟦X⟧}
    (hode : d⁄dX R H = G * H)
    (h0 : constantCoeff H = 0) : H = 0 := by
  have key : ∀ n, coeff n H = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => rw [coeff_zero_eq_constantCoeff_apply]; exact h0
      | m + 1 =>
        have hd := congrArg (coeff m) hode
        rw [coeff_derivative, coeff_mul,
          Finset.sum_eq_zero (fun p hp => ?_)] at hd
        · have hu : IsUnit ((m : R) + 1) := by
            simpa using
              (IsUnit.map (algebraMap ℚ R)
                (isUnit_iff_ne_zero.mpr (by positivity : ((m : ℚ) + 1) ≠ 0)))
          exact hu.mul_left_eq_zero.mp hd
        · rw [Finset.mem_antidiagonal] at hp
          rw [ih p.2 (by omega), mul_zero]
  ext n
  rw [key n, map_zero]

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

/-!
# Ch2 §II.2 — The labelled cycle closed form `CYC(C) = log(1/(1-C))`

`LabelledCyc.lean` characterizes the labelled cycle EGF by its ODE
`CYC(C)' = C'·SEQ(C)` together with a zero constant term
(`egf_lcyc_ode`, `egf_lcyc_unique`). The literal F&S closed form is

  `CYC(C)(z) = log(1 / (1 - C(z)))`.

Mathlib has no formal-power-series logarithm, so we deliver this in the
equivalent **exponentiated** shape, which needs only `PowerSeries.exp`
(already used for `egf_set`):

  `exp(CYC(C)) = 1/(1 - C(z)) = SEQ(C)`.

Both `exp(CYC(C))` and `SEQ(C)` solve the linear ODE `G' = CYC(C)'·G` with
constant term `1`, hence coincide by `ode_unique`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- `SEQ(C)` satisfies `SEQ(C)' = C'·SEQ(C)²`, obtained by differentiating the
defining relation `SEQ(C)·(1 - C) = 1`. -/
theorem CombClass.egf_lseq_deriv (C : CombClass) (hC : C.counts 0 = 0) :
    d⁄dX ℚ C.lseq.egf = d⁄dX ℚ C.egf * C.lseq.egf * C.lseq.egf := by
  set_option backward.isDefEq.respectTransparency false in
    have hlseq : C.lseq.egf * (1 - C.egf) = 1 := CombClass.egf_lseq C hC
    rw [(d⁄dX ℚ).leibniz_of_mul_eq_one hlseq]
    simp only [map_sub, Derivation.map_one_eq_zero, zero_sub, smul_eq_mul,
      neg_mul, mul_neg, neg_neg]
    ring

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
theorem solution (C : CombClass) (hC : C.counts 0 = 0) :
    (exp ℚ).subst C.lcyc.egf = C.lseq.egf := by
  set_option backward.isDefEq.respectTransparency false in
    have h0C : constantCoeff C.egf = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf, hC]; simp
    have hcyc0 : constantCoeff C.lcyc.egf = 0 := CombClass.constantCoeff_egf_lcyc C
    have hsubst : HasSubst C.lcyc.egf := by
      apply HasSubst.of_constantCoeff_zero'
      rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf]
      simp [CombClass.counts, CombClass.lcyc]
    -- `exp(CYC(C))` satisfies the chain-rule ODE `F' = CYC(C)'·F`.
    have hexp_ode :
        d⁄dX ℚ ((exp ℚ).subst C.lcyc.egf)
          = d⁄dX ℚ C.lcyc.egf * (exp ℚ).subst C.lcyc.egf := by
      rw [derivative_subst (hg := hsubst), derivative_exp]; ring
    -- The difference `H = exp(CYC(C)) - SEQ(C)` solves the homogeneous ODE.
    set H : ℚ⟦X⟧ := (exp ℚ).subst C.lcyc.egf - C.lseq.egf with hH
    have hode : d⁄dX ℚ H = (d⁄dX ℚ C.egf * C.lseq.egf) * H := by
      rw [hH, map_sub, hexp_ode, CombClass.egf_lcyc_ode C hC,
        CombClass.egf_lseq_deriv C hC]
      ring
    have h0subst : constantCoeff ((exp ℚ).subst C.lcyc.egf) = 1 := by
      change MvPowerSeries.constantCoeff (PowerSeries.subst C.lcyc.egf (PowerSeries.exp ℚ)) = 1
      rw [constantCoeff_subst hsubst, finsum_eq_single _ 0]
      · simp
      · intro d hd
        have hpow : MvPowerSeries.constantCoeff (C.lcyc.egf ^ d) = 0 := by
          change constantCoeff (C.lcyc.egf ^ d) = 0
          rw [map_pow, hcyc0, zero_pow hd]
        rw [hpow, smul_zero]
    have h0lseq : constantCoeff C.lseq.egf = 1 := by
      have h : constantCoeff (C.lseq.egf * (1 - C.egf)) = constantCoeff (1 : ℚ⟦X⟧) :=
        congrArg _ (CombClass.egf_lseq C hC)
      rwa [map_mul, map_sub, map_one, h0C, sub_zero, mul_one] at h
    have h0 : constantCoeff H = 0 := by
      rw [hH, map_sub, h0subst, h0lseq, sub_self]
    have hHzero : H = 0 := ode_unique hode h0
    rw [hH] at hHzero
    exact sub_eq_zero.mp hHzero
