-- Prove2me | solution 1 for AnalyticCombinatorics.undirectedCycleLogSqPermPairClass_counts_div_factorial_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:58:09.855995+00:00
-- url     : https://prove2.me/submissions/e2a48a35-53d9-4313-aabe-e59f3d245f79

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSingularity
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSqTransfer
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogTransfer
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularClass
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Alignments
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CycleMarkedPermPairs
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_UndirectedCycleLogSqPermPair
import Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_lcyc_unique
import Theorems.Thm_AnalyticCombinatorics_logSq_transfer_theorem_natural_remainder
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
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
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

@[simp] lemma coeff_ogfSeq (a : ℕ → ℕ) (n : ℕ) : coeff n (ogfSeq a) = (a n : ℚ) := by
  rw [ogfSeq, coeff_mk]

attribute [instance] CombClass.finObj

@[simp] lemma CombClass.coeff_ogf (C : CombClass) (n : ℕ) :
    coeff n C.ogf = (C.counts n : ℚ) := by
  rw [CombClass.ogf, coeff_ogfSeq]

/-! ### Primitive classes

We encode the primitive classes with `Obj n := Fin (· n)` so that the `Fintype`
instance is uniform; their entire content is their counting sequence. -/

@[simp] lemma CombClass.counts_empty (n : ℕ) : CombClass.empty.counts n = 0 :=
  Fintype.card_fin _

@[simp] lemma CombClass.counts_neutral (n : ℕ) :
    CombClass.neutral.counts n = if n = 0 then 1 else 0 :=
  Fintype.card_fin _

@[simp] lemma CombClass.counts_atom (n : ℕ) :
    CombClass.atom.counts n = if n = 1 then 1 else 0 :=
  Fintype.card_fin _

end AnalyticCombinatorics.Ch1
end

section
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

/-! ### Permutations -/

@[simp] lemma CombClass.counts_permutations (n : ℕ) :
    CombClass.permutations.counts n = n.factorial := by
  change Fintype.card (Equiv.Perm (Fin n)) = _
  rw [Fintype.card_perm, Fintype.card_fin]

/-! ### The set class -/

@[simp] lemma CombClass.counts_setClass (n : ℕ) : CombClass.setClass.counts n = 1 := by
  change Fintype.card Unit = _
  simp

end AnalyticCombinatorics.Ch1
end

section
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
end

section
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
end

section
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

attribute [local instance] AnalyticCombinatorics.Ch1.instTopRatLseq
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
end

section
open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

@[simp] lemma coeff_toFMLS (f : PowerSeries ℂ) (n : ℕ) :
    (toFMLS f).coeff n = PowerSeries.coeff (R := ℂ) n f := by
  simp [toFMLS]

@[simp] lemma coeff_mapℂ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (mapℂ f) =
      algebraMap ℚ ℂ (PowerSeries.coeff (R := ℚ) n f) := by
  simp [mapℂ]

@[simp] lemma nnnorm_toFMLS_apply (f : PowerSeries ℂ) (n : ℕ) :
    ‖toFMLS f n‖₊ = ‖PowerSeries.coeff (R := ℂ) n f‖₊ := by
  apply NNReal.eq
  simp [toFMLS]

end PowerSeries
end
end

section
/-!
# General-exponent singularity scale

This is the Flajolet--Sedgewick Theorem VI.1 standard scale for general `α`:
`[z^n] (1 - z)^{-α} ~ n^{α-1} / Γ(α)`. The integer case
`Γ(k) = (k - 1)!` is in `SingularityInteger.lean`; the full transfer theorem
with Δ-domains and a little-o Darboux estimate is assembled in
`TransferGeneral.lean` (`transfer_theorem`).

The hypothesis `∀ m : ℕ, α ≠ -m` says `α ∉ {0, -1, -2, ...}`. It holds for
all non-integer real `α` and is the correct non-vacuous hypothesis.
-/

open scoped BigOperators
open Finset Polynomial Filter Asymptotics

lemma ascPochhammer_eval_eq_prod_range_complex (n : ℕ) (r : ℂ) :
    Polynomial.eval r (ascPochhammer ℂ n) = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast, ih, Finset.prod_range_succ]

lemma choose_eq_prod_range_complex (α : ℂ) (n : ℕ) :
    Ring.choose (α + n - 1) n = (∏ j ∈ Finset.range n, (α + j)) / (n.factorial : ℂ) := by
  have hmul := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (R := ℂ) α n
  have hfac : (n.factorial : ℂ) * Ring.choose (α + n - 1) n =
      ∏ j ∈ Finset.range n, (α + j) := by
    rw [← Ring.multichoose_eq α n]
    simpa [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
      ascPochhammer_eval_eq_prod_range_complex] using hmul
  have hne : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hne]
  simpa [mul_comm] using hfac
end

section
open Complex Filter
open scoped Topology

lemma one_sub_mem_slitPlane_of_mem_delta {R φ : ℝ} {z : ℂ}
    (hφ0 : 0 < φ) (hz : z ∈ DeltaDomainArg R φ) :
    (1 - z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  have harg0 : Complex.arg (z - 1) = 0 := by
    rw [Complex.arg_eq_zero_iff]
    constructor
    · have hre := hnot.1
      simp at hre ⊢
      linarith
    · have him := hnot.2
      simp at him ⊢
      linarith
  have hlt : φ < 0 := by
    simpa [harg0] using hz.2.2
  linarith

lemma analyticOnNhd_one_sub_cpow_deltaDomain {α : ℂ} {R φ : ℝ}
    (hφ0 : 0 < φ) (_hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) := by
  exact (analyticOnNhd_const.sub analyticOnNhd_id).cpow analyticOnNhd_const
    (fun z hz => one_sub_mem_slitPlane_of_mem_delta hφ0 hz)
end

section
/-!
# The complex logarithm power series `−log(1−z) = ∑ zⁿ⁺¹/(n+1)`

Mathlib has only the *real* `Real.hasSum_pow_div_log_of_abs_lt_one`.  This file supplies the complex
analogue, the keystone bridge for the logarithmic singularity transfer (`LogTransfer`).

Reuses Mathlib's `Complex.logTaylor` remainder bound `norm_log_one_sub_inv_add_logTaylor_neg_le`:
the partial sums `∑_{j<N} zʲ⁺¹/(j+1) = −logTaylor(N+1)(−z)` converge to `log((1−z)⁻¹) = −log(1−z)`, and
the series is geometric-summable.
-/

open Filter Complex
open scoped Topology BigOperators

namespace AnalyticCombinatorics

/-- `logTaylor (N+1) (−z) = −∑_{n<N} zⁿ⁺¹/(n+1)`. -/
lemma logTaylor_neg_eq_neg_sum (N : ℕ) (z : ℂ) :
    Complex.logTaylor (N + 1) (-z)
      = -∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
  induction N with
  | zero => simp [Complex.logTaylor]
  | succ N ih =>
    have hterm : (-1 : ℂ) ^ (N + 1 + 1) * (-z) ^ (N + 1) / ((N + 1 : ℕ) : ℂ)
        = -(z ^ (N + 1) / ((N + 1 : ℕ) : ℂ)) := by
      have hne : ((-1 : ℂ)) ^ (N + 1 + 1) * (-1) ^ (N + 1) = -1 := by
        rw [← pow_add]; exact Odd.neg_one_pow ⟨N + 1, by ring⟩
      have hz1 : ((-z) ^ (N + 1) : ℂ) = (-1) ^ (N + 1) * z ^ (N + 1) := by rw [neg_pow]
      rw [hz1, ← mul_assoc, hne]
      push_cast
      ring
    rw [Complex.logTaylor_succ, Pi.add_apply, ih, hterm, Finset.sum_range_succ, neg_add]

/-- **Complex logarithm series**: for `‖z‖ < 1`, `∑ₙ zⁿ⁺¹/(n+1) = −log(1−z)`. -/
theorem hasSum_pow_succ_div_succ_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) (-Complex.log (1 - z)) := by
  have hmz : (0 : ℝ) < 1 - ‖z‖ := by linarith
  have hinv : (0 : ℝ) ≤ (1 - ‖z‖)⁻¹ := le_of_lt (inv_pos.mpr hmz)
  -- summability (dominated by the geometric series)
  have hgeo : Summable (fun n : ℕ => ‖z‖ ^ (n + 1)) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right ‖z‖
  have hsummable : Summable (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
    refine Summable.of_norm_bounded hgeo (fun n => ?_)
    rw [norm_div, norm_pow, Complex.norm_natCast]
    apply div_le_self (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  -- partial sums → -log(1-z)
  have harg : (1 - z).arg ≠ Real.pi := by
    have h := Complex.slitPlane_arg_ne_pi
      (Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by rwa [norm_neg]))
    rwa [sub_eq_add_neg]
  have hloginv : Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) := Complex.log_inv _ harg
  have htend0 : Tendsto
      (fun N : ℕ => Complex.log (1 - z)⁻¹ + Complex.logTaylor (N + 1) (-z)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hp : Tendsto (fun N : ℕ => ‖z‖ ^ (N + 1)) atTop (𝓝 0) := by
      simpa [pow_succ] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz).mul_const ‖z‖
    have hmaj : Tendsto (fun N : ℕ => ‖z‖ ^ (N + 1) * (1 - ‖z‖)⁻¹) atTop (𝓝 0) := by
      simpa using hp.mul_const ((1 - ‖z‖)⁻¹)
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hmaj
    refine (norm_log_one_sub_inv_add_logTaylor_neg_le N hz).trans ?_
    refine div_le_self (mul_nonneg (by positivity) hinv) ?_
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      atTop (𝓝 (-Complex.log (1 - z))) := by
    have h1 : Tendsto
        (fun N : ℕ => Complex.log (1 - z)⁻¹
          - ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
      simpa [logTaylor_neg_eq_neg_sum, sub_eq_add_neg] using htend0
    have h2 := (tendsto_const_nhds (α := ℕ) (x := Complex.log (1 - z)⁻¹)).sub h1
    simpa [hloginv] using h2
  -- assemble HasSum
  have hsum := hsummable.hasSum
  have hval : ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) = -Complex.log (1 - z) :=
    tendsto_nhds_unique hsum.tendsto_sum_nat htend
  rwa [hval] at hsum

end AnalyticCombinatorics
end

section
/-!
# Real-valued central-binomial and Catalan asymptotics

This file reflects the complex-valued asymptotic equivalents back to their
natural real-valued forms.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma ofReal_isEquivalent_iff {f g : ℕ → ℝ} :
    ((fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ))) ↔
      f ~[atTop] g := by
  constructor
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
end

section
/-!
# Logarithmic singularity scale

This file adds the coefficient scale for the first logarithmic singular factor
over the standard function `(1 - z)^{-α}`.

For real `α > 1`, the exact `n`-th coefficient of
`(1 - z)^{-α} log (1 / (1 - z))` is

`choose (α + n - 1) n * ∑_{j<n} (α + j)^{-1}`,

and it is asymptotic to `(n^(α - 1) / Γ α) * log n`.

The closed form is established directly from the exact parameter derivative of
the binomial coefficients (`logSingularityCoeff_isEquivalent`).  The final
section then proves the **genuine generating-function coefficient identity**
(`logSingularityCoeff_eq_coeff_logSingularityGF`): this closed form is exactly
the `n`-th coefficient of the Cauchy product of the honest power series for
`(1 - z)^{-α}` (Mathlib's `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`,
coefficients `Ring.choose (α + n - 1) n`) and for `log (1 / (1 - z))`
(coefficients `n⁻¹`), so the asymptotic is a genuine statement about the
log-singularity generating function rather than an asserted scale.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

/-!
## Genuine generating-function coefficient identity

The asymptotic above is stated for the *sequence*
`logSingularityCoeff α n = Ring.choose (α + n - 1) n * ∑_{j<n} (α + j)⁻¹`.
The purpose of this section is to prove that this sequence is genuinely the
coefficient sequence of the log-singularity generating function
`(1 - z)^{-α} · log (1 / (1 - z))`, rather than merely an asserted scale.

We work over `ℂ`, where the two factor generating functions have honest
coefficient descriptions:

* `[zⁿ] (1 - z)^{-α} = Ring.choose (α + n - 1) n` — this is exactly the
  `n`-th coefficient of the analytic power series of `fun z ↦ 1 / (1 - z)^α`
  at `0`, banked in Mathlib as
  `Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`, whose formal
  multilinear series is `.ofScalars ℂ (fun n ↦ Ring.choose (α + n - 1) n)`.
* `[zⁿ] log (1 / (1 - z)) = [zⁿ] (-log (1 - z)) = n⁻¹` for `n ≥ 1` and `0`
  for `n = 0` — this is the standard logarithm expansion
  `∑ n, z^{n+1}/(n+1) = -log (1 - z)` (`Real`/`Complex.hasSum_pow_div_log…`).

We package these as formal power series and prove, by the Cauchy product
(`PowerSeries.coeff_mul`) together with a binomial/partial-fraction identity,
that the `n`-th coefficient of the product equals
`Ring.choose (α + n - 1) n * ∑_{j<n} (α + j)⁻¹`, i.e. `logSingularityCoeff`.
-/

open scoped PowerSeries

/-- Recurrence for the binomial coefficients, from the product formula
`Ring.choose (α + n - 1) n = (∏ j < n, (α + j)) / n!`. -/
theorem binCoeffℂ_succ (α : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * binCoeffℂ α (n + 1) = (α + n) * binCoeffℂ α n := by
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hfac' : ((n + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  rw [binCoeffℂ, binCoeffℂ, choose_eq_prod_range_complex, choose_eq_prod_range_complex]
  rw [Finset.prod_range_succ]
  have hcast : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hcast]
  field_simp

end
end

section
/-!
# Discharging the model-faithfulness hypotheses of the logarithmic transfer

`log_transfer_theorem_strong_remainder` (LogTransfer) carries two model-faithfulness hypotheses for
`logSingularityFun α = (1−z)^{−α}·(−log(1−z))`:

* `hΔ_log` — delta-domain analyticity, and
* `hp_log` — its power series at `0` is `logSingularityGF α`.

This file discharges `hΔ_log` (mechanical, via `AnalyticOnNhd.clog` on the slit plane) and the
algebraic-factor half of `hp_log`.  The remaining piece of `hp_log` is the *complex* Taylor series
`−log(1−z) = ∑ zⁿ⁺¹/(n+1)` (Mathlib has only the real analogue) together with a Cauchy-product
realization — a genuine analytic bridge handled separately.
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- Delta-domain analyticity of the logarithmic factor `-log(1-z)` (principal branch). -/
lemma analyticOnNhd_negLog_one_sub_deltaDomain {R φ : ℝ} (hφ0 : 0 < φ) :
    AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) := by
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    (analyticOnNhd_const.sub analyticOnNhd_id).clog
      (fun z hz => one_sub_mem_slitPlane_of_mem_delta hφ0 hz)
  simpa [smul_eq_mul] using hlog.const_smul (c := (-1 : ℂ))

/-- **Discharges `hΔ_log`**: delta-domain analyticity of the log-singularity model. -/
lemma analyticOnNhd_logSingularityFun_deltaDomain {α : ℂ} {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (logSingularityFun α) (DeltaDomainArg R φ) := by
  have hpow : AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) :=
    analyticOnNhd_one_sub_cpow_deltaDomain (α := α) (R := R) (φ := φ) hφ0 hφπ
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    analyticOnNhd_negLog_one_sub_deltaDomain (R := R) (φ := φ) hφ0
  unfold logSingularityFun
  exact hpow.mul hlog

end
end

section
/-!
# Model faithfulness `hp_log` for the logarithmic transfer

Discharges the remaining hypothesis of `log_transfer_theorem_strong_remainder`:

  `logSingularityFun_hasFPowerSeriesAt : HasFPowerSeriesAt (logSingularityFun α) (toFMLS (logSingularityGF α)) 0`.

Route (ChatGPT-Pro R27): work directly via `hasFPowerSeriesAt_iff` and a per-`z` `HasSum`, avoiding the
absent `HasFPowerSeriesAt.mul`/FMLS multiplication and the radius computation.  The two factor series
(`oneSubCpowGF` from Mathlib's cpow series, `logGF` from `ComplexLogSeries`) are multiplied by an
ordinary Cauchy product (`hasSum_powerSeries_mul`), whose coefficient is `PowerSeries.coeff_mul`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators ENNReal NNReal

namespace AnalyticCombinatorics

lemma logCoeffℂ_eq_inv (n : ℕ) : logCoeffℂ n = (n : ℂ)⁻¹ := by
  cases n <;> simp [logCoeffℂ]

/-- The `logGF` coefficient series is norm-summable on the unit ball. -/
lemma logGF_summable_norm {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n logGF * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg z) hz)
  rw [norm_mul, norm_pow, logGF, PowerSeries.coeff_mk, logCoeffℂ_eq_inv]
  rcases n with _ | m
  · simp
  · rw [norm_inv, Complex.norm_natCast]
    calc (((m + 1 : ℕ) : ℝ))⁻¹ * ‖z‖ ^ (m + 1)
        ≤ 1 * ‖z‖ ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [inv_le_one_iff₀]; right; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)
      _ = ‖z‖ ^ (m + 1) := one_mul _
      _ ≤ ‖z‖ ^ (m + 1) := le_rfl

/-- `logGF` realizes `-log(1-z)` on the unit ball. -/
lemma logGF_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n logGF * z ^ n) (-Complex.log (1 - z)) := by
  have hraw := AnalyticCombinatorics.hasSum_pow_succ_div_succ_neg_log (z := z) hz
  have hzero : PowerSeries.coeff (R := ℂ) 0 logGF * z ^ 0 = 0 := by
    simp [logGF, logCoeffℂ]
  have htail : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) (n + 1) logGF * z ^ (n + 1))
      (-Complex.log (1 - z)) := by
    have : (fun n : ℕ => PowerSeries.coeff (R := ℂ) (n + 1) logGF * z ^ (n + 1))
        = fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
      funext n
      rw [logGF, PowerSeries.coeff_mk, logCoeffℂ_eq_inv]
      push_cast; ring
    rw [this]; exact hraw
  have hf0 : ∀ x ∉ Set.range Nat.succ,
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n logGF * z ^ n) x = 0 := by
    intro x hx
    rcases x with _ | m
    · simpa using hzero
    · exact absurd ⟨m, rfl⟩ hx
  exact (Function.Injective.hasSum_iff Nat.succ_injective hf0).mp htail

/-- The cpow factor `(1-z)^{-α}` realizes `oneSubCpowGF α` on the unit ball. -/
lemma oneSubCpowGF_hasSum {α z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) * z ^ n)
      ((1 - z) ^ (-α)) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α)
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [mem_emetric_ball_zero_iff, enorm_eq_nnnorm]
    exact_mod_cast hz
  have hsum := h.hasSum hzball
  rw [Complex.cpow_neg, inv_eq_one_div]
  simpa [oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm, zero_add] using hsum

/-- The cpow factor series is norm-summable on the unit ball. -/
lemma oneSubCpowGF_summable_norm {α z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) * z ^ n‖) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α)
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => Ring.choose (α + n - 1) n) with hp
  have hlt : (‖z‖₊ : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by exact_mod_cast hz) h.r_le
  refine (p.summable_norm_mul_pow hlt).congr (fun n => ?_)
  rw [norm_mul, norm_pow, hp, FormalMultilinearSeries.ofScalars_norm,
    oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ, coe_nnnorm]

/-- **Cauchy product** for ordinary `PowerSeries ℂ` evaluated at `z`, in `HasSum` form.
Replaces the absent `HasFPowerSeriesAt.mul`. -/
lemma hasSum_powerSeries_mul (F G : PowerSeries ℂ) {z A B : ℂ}
    (hF : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n F * z ^ n) A)
    (hG : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n G * z ^ n) B)
    (habsF : Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n F * z ^ n‖))
    (habsG : Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n G * z ^ n‖)) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n) (A * B) := by
  classical
  have hcoeff : ∀ n : ℕ,
      (∑ p ∈ Finset.antidiagonal n,
        (PowerSeries.coeff (R := ℂ) p.1 F * z ^ p.1) *
          (PowerSeries.coeff (R := ℂ) p.2 G * z ^ p.2))
        = PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_antidiagonal] at hp
    rw [← hp, pow_add]; ring
  have hval : A * B
      = ∑' n : ℕ, PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n := by
    rw [← hF.tsum_eq, ← hG.tsum_eq,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm habsF habsG]
    exact tsum_congr hcoeff
  have hsummable : Summable (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n) :=
    (summable_sum_mul_antidiagonal_of_summable_norm' habsF habsF.of_norm habsG habsG.of_norm).congr
      hcoeff
  rw [hval]; exact hsummable.hasSum

end AnalyticCombinatorics
end

section
/-!
# Squared-logarithm singularity transfer (strong-remainder form)

`(1-z)^{-α}·log²(1/(1-z))` with strong residual `o(|1-z|^{-α})` ⟹
`[zⁿ]f ~ C·n^{α-1}/Γ(α)·(log n)²`.

The model coefficient identity is `coeff_logSqGF_eq_logSqSingularityCoeffℂ` (LogSqCoeff) and the
real asymptotic is `logSqSingularityScale_isEquivalent` (LogSqSingularity).  As in the one-log
strong-remainder transfer, the residual error `o(n^{α-1})` from the algebraic Darboux descent is
absorbed into `o(n^{α-1}(log n)²)` — no new contour estimate.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics

/-- Norm-summability of the `logSingularityGF` coefficient series on the unit ball. -/
lemma logSingularityGF_summable_norm {α z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n (logSingularityGF α) * z ^ n‖) := by
  have hf := oneSubCpowGF_summable_norm (α := α) (z := z) hz
  have hg := logGF_summable_norm (z := z) hz
  have hfn : Summable (fun j : ℕ => ‖‖PowerSeries.coeff (R := ℂ) j (oneSubCpowGF α) * z ^ j‖‖) := by
    simpa using hf
  have hgn : Summable (fun k : ℕ => ‖‖PowerSeries.coeff (R := ℂ) k logGF * z ^ k‖‖) := by
    simpa using hg
  have hbig := summable_sum_mul_antidiagonal_of_summable_norm' hfn hf hgn hg
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbig
  rw [logSingularityGF, PowerSeries.coeff_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  rw [Finset.mem_antidiagonal] at hp
  have heq : PowerSeries.coeff (R := ℂ) p.1 (oneSubCpowGF α) *
        PowerSeries.coeff (R := ℂ) p.2 logGF * z ^ n
      = (PowerSeries.coeff (R := ℂ) p.1 (oneSubCpowGF α) * z ^ p.1) *
        (PowerSeries.coeff (R := ℂ) p.2 logGF * z ^ p.2) := by
    rw [← hp, pow_add]; ring
  rw [heq, norm_mul]

end AnalyticCombinatorics
end

section
open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Alignments

open AnalyticCombinatorics.Ch1

lemma coeff_cycleEGFℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n cycleEGFℂ = ((n : ℂ)⁻¹) := by
  simp [cycleEGFℂ]

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

theorem map_cycleEGFℚ :
    PowerSeries.mapℂ cycleEGFℚ = cycleEGFℂ := by
  ext n
  rw [PowerSeries.coeff_mapℂ, coeff_cycleEGFℚ, coeff_cycleEGFℂ]
  norm_num

end Alignments
end Meromorphic
end Ch5
end AnalyticCombinatorics
end
end

section
/-!
# A genuine labelled class with an `n log n` coefficient asymptotic

The labelled class

  `cycleMarkedPermPairClass := (CYC ⋆ SET(CYC)) ⋆ SET(CYC)`

— an ordered pair of permutations in which one cycle of the first permutation is
distinguished — has exponential generating function

  `A(z) = log(1/(1-z)) · 1/(1-z)² = (1-z)^{-2} · (-log(1-z))`,

which is exactly the logarithmic-singularity model `logSingularityFun 2`.  By the
unconditional strong-remainder logarithmic transfer
(`log_transfer_theorem_strong_remainder_unconditional`) at the clean point
`α = 2`, `C = 1`, with *zero* singular remainder, its normalized coefficients
satisfy

  `aₙ / n! ~ n · log n`   (since `Γ(2) = 1`).

This is the first application of the new unconditional log transfer to a genuine
labelled species.  All the analysis is banked: the only new work is
labelled-class / EGF plumbing, which reduces to the formal identity
`mapℂ A.egf = logSingularityGF 2`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-! ### Formal EGF identity `mapℂ A.egf = logSingularityGF 2` -/

/-- Over `ℂ`, the permutation EGF has all coefficients `1` (it is `(1-z)^{-1}`). -/
lemma coeff_mapℂ_permutations_egf (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (PowerSeries.mapℂ CombClass.permutations.egf) = 1 := by
  have h1 : PowerSeries.coeff (R := ℚ) n CombClass.permutations.egf = 1 := by
    rw [CombClass.coeff_egf, CombClass.counts_permutations,
      div_self (by exact_mod_cast Nat.factorial_ne_zero n)]
  rw [PowerSeries.coeff_mapℂ, h1, map_one]

/-- `logGF` (the `-log(1-z)` series) coincides with the labelled-cycle EGF `cycleEGFℂ`. -/
lemma logGF_eq_cycleEGFℂ : logGF = cycleEGFℂ := by
  ext n
  rw [logGF, PowerSeries.coeff_mk, coeff_cycleEGFℂ, logCoeffℂ]
  split_ifs with h
  · rw [h]; simp
  · rfl

/-- The binomial coefficients of `(1-z)^{-2}` are `n + 1`. -/
lemma binCoeffℂ_two (n : ℕ) : binCoeffℂ 2 n = (n : ℂ) + 1 := by
  induction n with
  | zero => simp [binCoeffℂ]
  | succ k ih =>
    have hrec := binCoeffℂ_succ 2 k
    rw [ih] at hrec
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : ((k : ℝ) + 1 : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast at h2 ⊢; exact h2
    have hcomm : (2 + (k : ℂ)) * ((k : ℂ) + 1) = ((k : ℂ) + 1) * (2 + (k : ℂ)) := by ring
    rw [hcomm] at hrec
    have hb : binCoeffℂ 2 (k + 1) = 2 + (k : ℂ) := mul_left_cancel₀ hk1 hrec
    rw [hb]; push_cast; ring

/-- The product of two permutation EGFs is `(1-z)^{-2}`, i.e. `oneSubCpowGF 2`. -/
lemma mapℂ_perm_sq_eq_oneSubCpowGF_two :
    PowerSeries.mapℂ CombClass.permutations.egf *
        PowerSeries.mapℂ CombClass.permutations.egf
      = oneSubCpowGF 2 := by
  ext n
  rw [PowerSeries.coeff_mul, oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ_two]
  have hterm : ∀ p ∈ Finset.antidiagonal n,
      PowerSeries.coeff (R := ℂ) p.1 (PowerSeries.mapℂ CombClass.permutations.egf) *
        PowerSeries.coeff (R := ℂ) p.2 (PowerSeries.mapℂ CombClass.permutations.egf) = 1 := by
    intro p _
    rw [coeff_mapℂ_permutations_egf, coeff_mapℂ_permutations_egf, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.Nat.card_antidiagonal,
    nsmul_eq_mul, mul_one]
  push_cast; ring

section
end

set_option backward.isDefEq.respectTransparency false in
/-- **Master EGF identity.** The complex EGF of the cycle-marked permutation-pair class
is the logarithmic-singularity generating function `(1-z)^{-2}·(-log(1-z))` at `α = 2`. -/
theorem mapℂ_cycleMarkedPermPairClass_egf :
    PowerSeries.mapℂ cycleMarkedPermPairClass.egf = logSingularityGF 2 := by
  rw [cycleMarkedPermPairClass, cycleMarkedPermClass,
    CombClass.egf_lprod, CombClass.egf_lprod, map_mul, map_mul,
    atom_lcyc_egf_eq_cycleEGFℚ, map_cycleEGFℚ, logSingularityGF, logGF_eq_cycleEGFℂ,
    mul_assoc, mapℂ_perm_sq_eq_oneSubCpowGF_two, mul_comm]

end AnalyticCombinatorics
end
end

section
/-!
# Genuine labelled class of two-regular graphs

A two-regular labelled graph is a labelled `SET` of undirected cycles of
length at least three.  The cycle carried by one block is modelled as a full
cycle permutation on the block labels, modulo reversing the orientation.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace TwoRegularClass

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

instance (n : ℕ) : DecidableEq (FullCyclePerm n) := by
  classical
  infer_instance

lemma fullCyclePerm_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (FullCyclePerm n) = (n - 1).factorial := by
  classical
  have hcycles := Equiv.Perm.card_of_cycleType_singleton
    (α := Fin n) (n := n) hn (by simp)
  have hsub :
      Fintype.card (FullCyclePerm n) =
        ({g | g.cycleType = ({n} : Multiset ℕ)} :
          Finset (Equiv.Perm (Fin n))).card := by
    unfold FullCyclePerm
    exact Fintype.subtype_card
      ({g | g.cycleType = ({n} : Multiset ℕ)} : Finset (Equiv.Perm (Fin n)))
      (by intro g; simp)
  rw [hsub, hcycles]
  simp

lemma fullCyclePerm_orderOf {n : ℕ} (c : FullCyclePerm n) :
    orderOf c.1 = n := by
  rw [← Equiv.Perm.lcm_cycleType c.1, c.2]
  simp

lemma fullCycleReverse_ne_of_three_le {n : ℕ} (hn : 3 ≤ n) (c : FullCyclePerm n) :
    fullCycleReverse c ≠ c := by
  intro h
  have hinv : c.1⁻¹ = c.1 := congrArg Subtype.val h
  have hsq : c.1 ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [← hinv]
    rw [mul_inv_cancel]
  have hdiv : n ∣ 2 := by
    rw [← fullCyclePerm_orderOf c]
    exact orderOf_dvd_of_pow_eq_one hsq
  exact not_le_of_gt (by omega : 2 < n) (Nat.le_of_dvd (by norm_num) hdiv)

lemma fixedBy_false_card (n : ℕ) :
    Fintype.card (AddAction.fixedBy (FullCyclePerm n) false) =
      Fintype.card (FullCyclePerm n) := by
  classical
  change Fintype.card {c : FullCyclePerm n // false +ᵥ c = c} =
    Fintype.card (FullCyclePerm n)
  exact Fintype.card_congr
    { toFun := fun c => c.1
      invFun := fun c => ⟨c, rfl⟩
      left_inv := fun c => by cases c; rfl
      right_inv := fun c => rfl }

lemma fixedBy_true_card_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    Fintype.card (AddAction.fixedBy (FullCyclePerm n) true) = 0 := by
  classical
  change Fintype.card {c : FullCyclePerm n // true +ᵥ c = c} = 0
  haveI : IsEmpty {c : FullCyclePerm n // true +ᵥ c = c} :=
    ⟨fun x => fullCycleReverse_ne_of_three_le hn x.1 (by simpa using x.2)⟩
  exact Fintype.card_eq_zero

lemma undirectedCycle_card_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    Fintype.card (UndirectedCycle n) = (n - 1).factorial / 2 := by
  classical
  have hburn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    Bool (FullCyclePerm n)
  rw [Fintype.sum_bool, fixedBy_false_card, fixedBy_true_card_of_three_le hn,
    fullCyclePerm_card (by omega : 2 ≤ n), Fintype.card_bool, zero_add] at hburn
  exact Nat.eq_div_of_mul_eq_right (by norm_num : 2 ≠ 0)
    (by simpa [UndirectedCycle, mul_comm] using hburn.symm)

@[simp] lemma undirectedCycleClass_counts (n : ℕ) :
    undirectedCycleClass.counts n =
      if 3 ≤ n then (n - 1).factorial / 2 else 0 := by
  classical
  by_cases h : 3 ≤ n
  · simp [undirectedCycleClass, CombClass.counts, h, undirectedCycle_card_of_three_le h]
  · simp [undirectedCycleClass, CombClass.counts, h]

@[simp] lemma undirectedCycleClass_counts_zero :
    undirectedCycleClass.counts 0 = 0 := by
  simp

lemma undirectedCycleClass_coeff_egf_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℚ) n undirectedCycleClass.egf =
      (1 : ℚ) / (2 * n) := by
  rw [CombClass.coeff_egf, undirectedCycleClass_counts, if_pos hn]
  have hn0 : n ≠ 0 := by omega
  have hfac : n.factorial = n * (n - 1).factorial := by
    cases n with
    | zero => contradiction
    | succ m =>
        simp [Nat.factorial_succ, Nat.mul_comm]
  have hcard := undirectedCycle_card_of_three_le hn
  have hburn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    Bool (FullCyclePerm n)
  rw [Fintype.sum_bool, fixedBy_false_card, fixedBy_true_card_of_three_le hn,
    fullCyclePerm_card (by omega : 2 ≤ n), Fintype.card_bool, zero_add] at hburn
  change (n - 1).factorial = Fintype.card (UndirectedCycle n) * 2 at hburn
  have hmul_nat : Fintype.card (UndirectedCycle n) * 2 = (n - 1).factorial := by
    exact hburn.symm
  have hhalf_mul_nat : ((n - 1).factorial / 2) * 2 = (n - 1).factorial := by
    rw [← hcard]
    exact hmul_nat
  have hmul_rat : (((n - 1).factorial / 2 : ℕ) : ℚ) * 2 =
      ((n - 1).factorial : ℚ) := by
    exact_mod_cast hhalf_mul_nat
  have hhalf_rat :
      (((n - 1).factorial / 2 : ℕ) : ℚ) =
        ((n - 1).factorial : ℚ) / 2 := by
    nlinarith
  rw [hfac]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hfnq : (((n - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  have h2q : (2 : ℚ) ≠ 0 := by norm_num
  rw [hhalf_rat]
  field_simp [hnq, hfnq, h2q]
  norm_num [Nat.cast_mul]
  ring

lemma undirectedCycleClass_coeff_egf_of_lt_three {n : ℕ} (hn : n < 3) :
    PowerSeries.coeff (R := ℚ) n undirectedCycleClass.egf = 0 := by
  rw [CombClass.coeff_egf, undirectedCycleClass_counts, if_neg (by omega)]
  simp

section
end

set_option backward.isDefEq.respectTransparency false in
/-- The core EGF is half the directed cycle EGF, with sizes one and two removed. -/
theorem undirectedCycleClass_egf :
    undirectedCycleClass.egf =
      (2⁻¹ : ℚ) • cycleEGFℚ -
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) -
          (4⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
  ext n
  by_cases hn : 3 ≤ n
  · rw [undirectedCycleClass_coeff_egf_of_three_le hn]
    rw [map_sub, map_sub, map_smul, map_smul, map_smul, coeff_cycleEGFℚ]
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow, hn1, hn2]
    field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0)]
  · have hnlt : n < 3 := by omega
    rw [undirectedCycleClass_coeff_egf_of_lt_three hnlt]
    interval_cases n
    · simp [cycleEGFℚ_constantCoeff]
    · simp [coeff_cycleEGFℚ, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    · norm_num [coeff_cycleEGFℚ, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

/-! ### Complex analytic bridge to the singularity-analysis file -/

/-- The complex core EGF for one undirected cycle block. -/
def twoRegularCoreEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ undirectedCycleClass.egf

/-- The closed complex core series. -/
def twoRegularCoreSeriesℂ : PowerSeries ℂ :=
  (2⁻¹ : ℂ) • cycleEGFℂ -
    (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) -
      (4⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2

section
end

set_option backward.isDefEq.respectTransparency false in
lemma twoRegularCoreEGFℂ_eq :
    twoRegularCoreEGFℂ = twoRegularCoreSeriesℂ := by
  unfold twoRegularCoreEGFℂ twoRegularCoreSeriesℂ
  rw [undirectedCycleClass_egf]
  ext n
  simp [PowerSeries.coeff_mapℂ, coeff_cycleEGFℚ, coeff_cycleEGFℂ]
  by_cases h1 : n = 1
  · subst n
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  · by_cases h2 : n = 2
    · subst n
      simp [PowerSeries.coeff_X]
    · simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow, h1, h2]

/-- Analytic representative of the one-block EGF near zero. -/
def twoRegularCoreFun : ℂ → ℂ :=
  (2⁻¹ : ℂ) • cycleAnalyticFun -
    (2⁻¹ : ℂ) • (fun z : ℂ => z) -
      (4⁻¹ : ℂ) • (fun z : ℂ => z ^ 2)

end TwoRegularClass
end
end

section
/-!
# A labelled class that genuinely needs the natural-remainder log transfer

`cycleMarkedPermPairClass` (CycleMarkedPermPairs.lean) had EGF *exactly*
`(1-z)^{-2}(-log(1-z))` — zero singular remainder — so it did not distinguish the
natural-remainder transfer from the strong one.  This file gives the first class that
**only** the natural-remainder transfer can handle:

  `A := (undirectedCycleClass ⋆ permutations) ⋆ permutations`

— an ordered pair of permutations carrying one distinguished *undirected* cycle of length
≥ 3 — with EGF

  `A(z) = (½·log(1/(1-z)) - z/2 - z²/4)·(1-z)^{-2}`
        `= ½·(1-z)^{-2}(-log(1-z))  -  (z/2 + z²/4)(1-z)^{-2}`.

The residual `-(z/2+z²/4)(1-z)^{-2}` satisfies `‖residual‖·‖1-z‖² → 3/4 ≠ 0` (so it is
NOT `o(|1-z|^{-2})` — the strong-remainder transfer fails), but `‖residual‖·‖1-z‖²/log(1/‖1-z‖) → 0`
(so the natural-remainder transfer applies).  Hence

  `aₙ / n! ~ ½·n·log n`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-! ### Formal EGF identity `mapℂ A.egf = twoRegularCoreEGFℂ · oneSubCpowGF 2` -/

/-! ### Per-`z` realization of `twoRegularCoreEGFℂ` (for the Cauchy product) -/

/-- `twoRegularCoreEGFℂ` realizes `twoRegularCoreFun` on the unit ball. -/
lemma twoRegularCore_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ * z ^ n)
      (TwoRegularClass.twoRegularCoreFun z) := by
  have hcyc : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n cycleEGFℂ * z ^ n) (-Complex.log (1 - z)) := by
    rw [show cycleEGFℂ = logGF from (logGF_eq_cycleEGFℂ).symm]; exact logGF_hasSum hz
  have hX : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ) * z ^ n) z := by
    have h := hasSum_single (b := 1)
      (f := fun n : ℕ => PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ) * z ^ n)
      (fun n hn => by simp [PowerSeries.coeff_X, hn])
    simpa [PowerSeries.coeff_X] using h
  have hX2 : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2) * z ^ n)
      (z ^ 2) := by
    have h := hasSum_single (b := 2)
      (f := fun n : ℕ => PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2) * z ^ n)
      (fun n hn => by simp [PowerSeries.coeff_X_pow, hn])
    simpa [PowerSeries.coeff_X_pow] using h
  have hval : (2⁻¹ : ℂ) * (-Complex.log (1 - z)) - 2⁻¹ * z - 4⁻¹ * z ^ 2
      = TwoRegularClass.twoRegularCoreFun z := by
    simp only [TwoRegularClass.twoRegularCoreFun, cycleAnalyticFun, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  have hfun : (fun n : ℕ => PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ * z ^ n)
      = (fun n : ℕ => (2⁻¹ : ℂ) * (PowerSeries.coeff (R := ℂ) n cycleEGFℂ * z ^ n)
          - (2⁻¹ : ℂ) * (PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ) * z ^ n)
          - (4⁻¹ : ℂ) * (PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2)
              * z ^ n)) := by
    funext n
    rw [TwoRegularClass.twoRegularCoreEGFℂ_eq, TwoRegularClass.twoRegularCoreSeriesℂ]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  rw [hfun, ← hval]
  exact ((hcyc.mul_left (2⁻¹ : ℂ)).sub (hX.mul_left (2⁻¹ : ℂ))).sub (hX2.mul_left (4⁻¹ : ℂ))

/-- `twoRegularCoreEGFℂ` factor series is norm-summable on the unit ball. -/
lemma twoRegularCore_summable_norm {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ * z ^ n‖) := by
  have hgeo := summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.mul_left (5 / 4))
  rw [norm_mul, norm_pow]
  have hnorm_half : ‖(2⁻¹ : ℂ)‖ = 2⁻¹ := by rw [norm_inv]; norm_num [Complex.norm_ofNat]
  have hnorm_quart : ‖(4⁻¹ : ℂ)‖ = 4⁻¹ := by rw [norm_inv]; norm_num [Complex.norm_ofNat]
  have hcoeff : ‖PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ‖ ≤ 5 / 4 := by
    rw [TwoRegularClass.twoRegularCoreEGFℂ_eq, TwoRegularClass.twoRegularCoreSeriesℂ]
    simp only [map_sub, map_smul, smul_eq_mul, coeff_cycleEGFℂ]
    have ha : ‖(2⁻¹ : ℂ) * (n : ℂ)⁻¹‖ ≤ 2⁻¹ := by
      rw [norm_mul, hnorm_half]
      have hn1 : ‖((n : ℂ))⁻¹‖ ≤ 1 := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · rw [norm_inv, Complex.norm_natCast, inv_le_one_iff₀]; right; exact_mod_cast hn
      nlinarith [hn1, norm_nonneg ((n : ℂ)⁻¹)]
    have hb : ‖(2⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ)‖ ≤ 2⁻¹ := by
      rw [norm_mul, hnorm_half]
      have : ‖PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ)‖ ≤ 1 := by
        rw [PowerSeries.coeff_X]; split <;> simp
      nlinarith [this, norm_nonneg (PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ))]
    have hc : ‖(4⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2)‖
        ≤ 4⁻¹ := by
      rw [norm_mul, hnorm_quart]
      have : ‖PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2)‖ ≤ 1 := by
        rw [PowerSeries.coeff_X_pow]; split <;> simp
      nlinarith [this,
        norm_nonneg (PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2))]
    have htri : ‖(2⁻¹ : ℂ) * (n : ℂ)⁻¹ - 2⁻¹ * PowerSeries.coeff (R := ℂ) n PowerSeries.X
          - 4⁻¹ * PowerSeries.coeff (R := ℂ) n (PowerSeries.X ^ 2)‖
        ≤ ‖(2⁻¹ : ℂ) * (n : ℂ)⁻¹‖
          + ‖(2⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n PowerSeries.X‖
          + ‖(4⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n (PowerSeries.X ^ 2)‖ := by
      have h1 := norm_sub_le ((2⁻¹ : ℂ) * (n : ℂ)⁻¹
        - 2⁻¹ * PowerSeries.coeff (R := ℂ) n PowerSeries.X)
        ((4⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n (PowerSeries.X ^ 2))
      have h2 := norm_sub_le ((2⁻¹ : ℂ) * (n : ℂ)⁻¹)
        ((2⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n PowerSeries.X)
      linarith
    linarith [htri, ha, hb, hc]
  calc ‖PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ‖ * ‖z‖ ^ n
      ≤ (5 / 4) * ‖z‖ ^ n := mul_le_mul_of_nonneg_right hcoeff (by positivity)

end AnalyticCombinatorics
end
end

/-!
# A class that GENUINELY needs the natural-remainder log² transfer (~½·n·(log n)²)

`undirectedCycleLogSqPermPairClass := undirectedCycleClass ⋆ cycleMarkedPermPairClass` — an
undirected cycle (length ≥ 3) together with an ordered pair of permutations one of whose cycles is
distinguished — has EGF

  `(½·log(1/(1-z)) - z/2 - z²/4) · log(1/(1-z)) · (1-z)^{-2}`
    `= ½·(1-z)^{-2}·(-log(1-z))²  -  (z/2 + z²/4)·(1-z)^{-2}·(-log(1-z))`.

The residual `R(z) = -(z/2+z²/4)·(1-z)^{-2}·(-log(1-z))` has `‖R‖·‖1-z‖² ≍ |log(1-z)| → ∞`
(so it is NOT `o(|1-z|^{-2})` — the *strong* log² transfer fails), yet
`‖R‖·‖1-z‖²/log²(1/|1-z|) → 0` (so the *natural* log² transfer applies).  Hence

  `aₙ / n! ~ ½·n·(log n)²`.

This is the first class requiring the natural-remainder log² transfer (analog of
`undirectedCycleMarkedPermPairs` for log¹).  (Construction from ChatGPT-Pro ac/ac2.)
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

theorem mapℂ_undirectedCycleLogSqPermPairClass_egf :
    PowerSeries.mapℂ undirectedCycleLogSqPermPairClass.egf
      = TwoRegularClass.twoRegularCoreEGFℂ * logSingularityGF 2 := by
  rw [undirectedCycleLogSqPermPairClass, CombClass.egf_lprod, map_mul,
    mapℂ_cycleMarkedPermPairClass_egf, TwoRegularClass.twoRegularCoreEGFℂ]

/-- Analytic carrier `twoRegularCoreFun(z)·logSingularityFun 2 z`. -/
def undirectedCycleLogSqPermPairFun (z : ℂ) : ℂ :=
  TwoRegularClass.twoRegularCoreFun z * logSingularityFun ((2 : ℝ) : ℂ) z

/-- `twoRegularCoreFun` is `Δ`-analytic. -/
lemma analyticOnNhd_twoRegularCoreFun_deltaDomain {R φ : ℝ} (hφ0 : 0 < φ) :
    AnalyticOnNhd ℂ TwoRegularClass.twoRegularCoreFun (DeltaDomainArg R φ) := by
  have hneglog : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    analyticOnNhd_negLog_one_sub_deltaDomain hφ0
  have hfeq : TwoRegularClass.twoRegularCoreFun
      = fun z : ℂ => (2⁻¹ : ℂ) * (-Complex.log (1 - z)) - (2⁻¹ : ℂ) * z - (4⁻¹ : ℂ) * z ^ 2 := by
    funext z
    simp only [TwoRegularClass.twoRegularCoreFun, cycleAnalyticFun, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hfeq]
  exact ((analyticOnNhd_const.mul hneglog).sub (analyticOnNhd_const.mul analyticOnNhd_id)).sub
    (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2))

lemma analyticOnNhd_undirectedCycleLogSqPermPairFun_deltaDomain {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ undirectedCycleLogSqPermPairFun (DeltaDomainArg R φ) :=
  (analyticOnNhd_twoRegularCoreFun_deltaDomain hφ0).mul
    (analyticOnNhd_logSingularityFun_deltaDomain hφ0 hφπ)

/-- Faithfulness: power series of the carrier is `mapℂ A.egf` (double Cauchy product). -/
lemma undirectedCycleLogSqPermPairFun_hasFPowerSeriesAt :
    HasFPowerSeriesAt undirectedCycleLogSqPermPairFun
      (PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleLogSqPermPairClass.egf)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hlogModel := hasSum_powerSeries_mul (oneSubCpowGF (2 : ℂ)) logGF
    (oneSubCpowGF_hasSum (α := (2 : ℂ)) hz_norm) (logGF_hasSum hz_norm)
    (oneSubCpowGF_summable_norm (α := (2 : ℂ)) hz_norm) (logGF_summable_norm hz_norm)
  rw [← logSingularityGF] at hlogModel
  have hprod := hasSum_powerSeries_mul TwoRegularClass.twoRegularCoreEGFℂ (logSingularityGF (2 : ℂ))
    (twoRegularCore_hasSum hz_norm) hlogModel
    (twoRegularCore_summable_norm hz_norm) (logSingularityGF_summable_norm (α := (2 : ℂ)) hz_norm)
  rw [← mapℂ_undirectedCycleLogSqPermPairClass_egf] at hprod
  have hval : TwoRegularClass.twoRegularCoreFun z * ((1 - z) ^ (-(2 : ℂ)) * -Complex.log (1 - z))
      = undirectedCycleLogSqPermPairFun z := by
    rw [undirectedCycleLogSqPermPairFun, logSingularityFun,
      show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  rw [hval] at hprod
  simpa [PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm] using hprod

/-- The residual identity `f - ½·logSqModel = -(½z+¼z²)·logSingularityFun 2`. -/
lemma undirectedCycleLogSqPermPairFun_residual (z : ℂ) :
    undirectedCycleLogSqPermPairFun z - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) z
      = -((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2) * logSingularityFun ((2 : ℝ) : ℂ) z := by
  simp only [undirectedCycleLogSqPermPairFun, TwoRegularClass.twoRegularCoreFun, cycleAnalyticFun,
    logSqSingularityFun, logSingularityFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  ring

/-- `‖-log(1-z)‖ / log²(1/‖1-z‖) → 0` near `1`. -/
lemma negLog_over_logSq_tendsto_zero {R φ : ℝ} :
    Tendsto (fun z : ℂ => ‖-Complex.log (1 - z)‖ * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
  have hnorm0 : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖) (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have h : Continuous (fun z : ℂ => ‖(1 : ℂ) - z‖) := by fun_prop
    simpa using h.tendsto 1
  have hLatTop : Tendsto (fun z : ℂ => Real.log (‖(1 : ℂ) - z‖⁻¹))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) atTop := by
    have hinv : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖⁻¹) (𝓝[DeltaDomainArg R φ] (1 : ℂ)) atTop := by
      apply Filter.Tendsto.comp tendsto_inv_nhdsGT_zero
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hnorm0, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz.2.1))
    exact Real.tendsto_log_atTop.comp hinv
  -- upper bound (L+π)/L² → 0
  have hub : Tendsto (fun z : ℂ => (Real.log (‖(1 : ℂ) - z‖⁻¹) + Real.pi)
      * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹) (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    have hcomp : Tendsto (fun L : ℝ => (L + Real.pi) * (L ^ 2)⁻¹) atTop (𝓝 0) := by
      have : (fun L : ℝ => (L + Real.pi) * (L ^ 2)⁻¹) =ᶠ[atTop]
          (fun L : ℝ => L⁻¹ + Real.pi * (L ^ 2)⁻¹) := by
        filter_upwards [eventually_gt_atTop 0] with L hL
        field_simp
      rw [tendsto_congr' this]
      have h1 : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have h2 : Tendsto (fun L : ℝ => Real.pi * (L ^ 2)⁻¹) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp
          (tendsto_pow_atTop (by norm_num : 2 ≠ 0))).const_mul Real.pi
        simpa using this
      simpa using h1.add h2
    exact hcomp.comp hLatTop
  refine squeeze_zero' (Eventually.of_forall fun z => by positivity) ?_ hub
  filter_upwards [hnorm0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    self_mem_nhdsWithin] with z hz1 hzΔ
  have hz_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzΔ.2.1)
  have hnpos : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr hz_ne
  have hn1 : ‖(1 : ℂ) - z‖ < 1 := by simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hz1
  have hLpos : 0 < Real.log (‖(1 : ℂ) - z‖⁻¹) := by
    rw [Real.log_inv]; have := Real.log_neg hnpos hn1; linarith
  have hlogbound : ‖-Complex.log (1 - z)‖ ≤ Real.log (‖(1 : ℂ) - z‖⁻¹) + Real.pi := by
    rw [norm_neg]
    have h1 : ‖Complex.log (1 - z)‖
        ≤ |(Complex.log (1 - z)).re| + |(Complex.log (1 - z)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [Complex.log_re, Complex.log_im] at h1
    have harg : |Complex.arg (1 - z)| ≤ Real.pi := Complex.abs_arg_le_pi _
    have hlog : |Real.log ‖(1 : ℂ) - z‖| = Real.log (‖(1 : ℂ) - z‖⁻¹) := by
      rw [Real.log_inv, abs_of_neg (Real.log_neg hnpos hn1)]
    rw [hlog] at h1; linarith
  exact mul_le_mul_of_nonneg_right hlogbound (by positivity)

end AnalyticCombinatorics
end

open AnalyticCombinatorics
open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology
open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments
theorem solution :
    (fun n : ℕ => (undirectedCycleLogSqPermPairClass.counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => (1 / 2 : ℝ) * (n : ℝ) * (Real.log n) ^ 2) := by
  set R : ℝ := 2 with hR_def
  set φ : ℝ := Real.pi / 4 with hφ_def
  have hφ0 : 0 < φ := by rw [hφ_def]; positivity
  have hφ2 : φ < Real.pi / 2 := by rw [hφ_def]; linarith [Real.pi_pos]
  have hφπ : φ < Real.pi := by linarith [Real.pi_pos]
  have hsing : Tendsto
      (fun z : ℂ => ‖undirectedCycleLogSqPermPairFun z
          - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (2 : ℝ)
        * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    have hpoly : Tendsto (fun z : ℂ => ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖)
        (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 ‖(1 / 2 : ℂ) * 1 + (1 / 4 : ℂ) * 1 ^ 2‖) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (Continuous.norm (by fun_prop)).tendsto 1
    have hmul := hpoly.mul (negLog_over_logSq_tendsto_zero (R := R) (φ := φ))
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.2.1)
    have hnz : ‖(1 : ℂ) - z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
    have hcpow : ‖logSingularityFun ((2 : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (2 : ℝ)
        = ‖-Complex.log (1 - z)‖ := by
      have hr2 : ‖(1 : ℂ) - z‖ ^ (2 : ℝ) = ‖(1 : ℂ) - z‖ ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [logSingularityFun, show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, Complex.cpow_neg,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, norm_mul, norm_inv,
        norm_pow, hr2, mul_right_comm, inv_mul_cancel₀ (pow_ne_zero 2 hnz), one_mul]
    rw [undirectedCycleLogSqPermPairFun_residual, norm_mul,
      show ‖-((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2)‖ = ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖
        from norm_neg _, ← hcpow]
    ring
  have htransfer := logSq_transfer_theorem_natural_remainder
    (α := (2 : ℝ)) (C := (1 / 2 : ℂ)) (R := R) (φ := φ)
    (f := undirectedCycleLogSqPermPairFun)
    (p := PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleLogSqPermPairClass.egf))
    (by norm_num) (by norm_num) (by rw [hR_def]; norm_num) hφ0 hφ2
    undirectedCycleLogSqPermPairFun_hasFPowerSeriesAt
    (analyticOnNhd_undirectedCycleLogSqPermPairFun_deltaDomain hφ0 hφπ)
    hsing
  have hLHS : (fun n : ℕ =>
        (PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleLogSqPermPairClass.egf)).coeff n)
      = (fun n : ℕ =>
          (((undirectedCycleLogSqPermPairClass.counts n : ℝ) / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 / 2 : ℂ) *
        (((n : ℝ) ^ ((2 : ℝ) - 1) / Real.Gamma 2 * (Real.log n) ^ 2 : ℝ) : ℂ))
      = (fun n : ℕ => (((1 / 2 : ℝ) * (n : ℝ) * (Real.log n) ^ 2 : ℝ) : ℂ)) := by
    funext n
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.Gamma_two, div_one]
    push_cast; ring
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer
