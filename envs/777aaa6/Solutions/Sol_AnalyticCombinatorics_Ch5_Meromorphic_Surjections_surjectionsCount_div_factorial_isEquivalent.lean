-- Prove2me | solution 1 for AnalyticCombinatorics.Ch5.Meromorphic.Surjections.surjectionsCount_div_factorial_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T20:09:04.95443+00:00
-- url     : https://prove2.me/submissions/62132b64-f8ab-4e52-b458-c853442acc40

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Surjections
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
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
# Ch1 §I.2 / §I.3 — The sequence construction and integer compositions

Flajolet & Sedgewick, Part A, Chapter I. The sequence construction `SEQ(C)` forms
all finite sequences `(γ₁, …, γₘ)` of `C`-objects, with size the sum of the
component sizes. For this to give a (finite) combinatorial class one needs `C` to
have no object of size `0` (F&S's standing side-condition); the positive
component sizes of a size-`n` sequence then form a *composition* of `n`, so we
model `SEQ(C)` over Mathlib's `Composition n`.

This file proves, at the level of counting sequences, the genuine combinatorial
content:

* `counts_seq` — `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
* `counts_seq_posInt` — **integer compositions are sequences of positive
  integers** (F&S §I.3): `(SEQ ℙ)ₙ = #(Composition n) = 2^{n-1}`.

The closed-form generating function of compositions lives in `Compositions.lean`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

@[simp] lemma CombClass.counts_posInt (n : ℕ) :
    CombClass.posInt.counts n = if 0 < n then 1 else 0 :=
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
# Ch2 §II.3 — Applications of the labelled symbolic method

Flajolet & Sedgewick, Part A, Chapter II, §II.3. Using the labelled set and
sequence transfers on the positive-integer ("urn"/nonempty-block) class `ℙ`
(one object of each size `n ≥ 1`, EGF `e^z - 1`):

* set partitions / **Bell numbers** `SET(ℙ)`, EGF `exp(e^z - 1)`;
* **surjections** `SEQ(ℙ)`, EGF `1/(2 - e^z)`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The EGF of the positive-integer (nonempty-block) class is `e^z - 1`. -/
theorem CombClass.egf_posInt : CombClass.posInt.egf = PowerSeries.exp ℚ - 1 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_posInt, map_sub, coeff_exp, coeff_one]
  rcases n with _ | m <;> simp

/-- **Surjections** (F&S §II.3): `SEQ(ℙ)(z)·(2 - e^z) = 1`, i.e. `1/(2 - e^z)`. -/
theorem CombClass.egf_surjections :
    CombClass.posInt.lseq.egf * (1 - (PowerSeries.exp ℚ - 1)) = 1 := by
  have h := CombClass.egf_lseq CombClass.posInt (by simp [CombClass.counts_posInt])
  rwa [CombClass.egf_posInt] at h

end AnalyticCombinatorics.Ch1

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

end PowerSeries
end

open Complex
open scoped NNReal ENNReal

noncomputable section

theorem coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi * I : ℂ)⁻¹ •
        circleIntegral
          (fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
          0 R := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R) 0 := by
    have hnn : 0 < ((⟨R, hR.le⟩ : ℝ≥0)) := by
      exact_mod_cast hR
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f 0 R := hp.eq_formalMultilinearSeries hq
  calc
    p.coeff n = (cauchyPowerSeries f 0 R).coeff n := by rw [hpq]
    _ = (cauchyPowerSeries f 0 R n fun _ => (1 : ℂ)) := by rfl
    _ = _ := by exact cauchyPowerSeries_apply f 0 R n 1

theorem norm_coeff_le_of_circleIntegral
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R M : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖p.coeff n‖ ≤ M * R⁻¹ ^ n := by
  let g : ℂ → ℂ := fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z
  have hcoeff :
      p.coeff n = (2 * Real.pi * I : ℂ)⁻¹ • circleIntegral g 0 R := by
    simpa [g] using coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt hR hp hd n
  rw [hcoeff]
  calc
    ‖(2 * Real.pi * I : ℂ)⁻¹ • circleIntegral g 0 R‖
        ≤ R * (M * R⁻¹ ^ (n + 1)) := by
      refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        hR.le ?_
      intro z hz
      have hz_norm : ‖z‖ = R := by
        simpa using (Metric.mem_sphere.1 hz)
      calc
        ‖g z‖ = R⁻¹ ^ n * R⁻¹ * ‖f z‖ := by
          simp [g, norm_pow, div_eq_mul_inv, hz_norm, inv_pow, mul_assoc]
        _ ≤ R⁻¹ ^ n * R⁻¹ * M := by
          exact mul_le_mul_of_nonneg_left (hM z hz)
            (mul_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) n)
              (inv_nonneg.mpr hR.le))
        _ = M * R⁻¹ ^ (n + 1) := by
          rw [pow_succ]
          ring
    _ = M * R⁻¹ ^ n := by
      rw [pow_succ]
      field_simp [hR.ne']

end

open Filter Asymptotics
open scoped PowerSeries Topology BigOperators

noncomputable section

namespace PowerSeries

lemma coeff_rescale_invUnitsSub_one (a : ℂ) (n : ℕ) :
    coeff (R := ℂ) n (rescale a (invUnitsSub (1 : ℂˣ))) = a ^ n := by
  simp [coeff_rescale]

end PowerSeries
end

open scoped BigOperators PowerSeries
open List Finset

noncomputable section

namespace FormalMultilinearSeries

lemma ofScalars_comp_coeff (a b : ℕ → ℂ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ a).comp
      (FormalMultilinearSeries.ofScalars ℂ b)).coeff n =
      ∑ c : Composition n, a c.length * ∏ i : Fin c.length, b (c.blocksFun i) := by
  rw [FormalMultilinearSeries.coeff]
  simp [FormalMultilinearSeries.comp, FormalMultilinearSeries.applyComposition,
    FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn, smul_eq_mul]

end FormalMultilinearSeries

private lemma prod_coeff_eq_zero_of_not_pos {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0)
    {d n : ℕ} (l : { l : Fin d → ℕ // ∑ i, l i = n })
    (hl : ¬ ∀ i, 0 < l.1 i) :
    (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) = 0 := by
  classical
  push Not at hl
  rcases hl with ⟨i, hi⟩
  have hzero : l.1 i = 0 := Nat.eq_zero_of_le_zero hi
  rw [Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [hzero]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg

private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {g : ℂ⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    {n d : ℕ} (hnd : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    exact PowerSeries.coeff_of_lt_order n
      (lt_of_lt_of_le (by exact_mod_cast hnd)
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg))

private lemma coeff_pow_eq_sum_composition_length {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (d n : ℕ) :
    PowerSeries.coeff n (g ^ d) =
      ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
  classical
  rw [PowerSeries.coeff_pow]
  let A := (Finset.range d).finsuppAntidiag n
  let B := { l : Fin d → ℕ // ∑ i, l i = n }
  letI : Fintype B := Fintype.ofEquiv A (finsuppAntidiagRangeEquivFin n d)
  let P : B → Prop := fun l => ∀ i, 0 < l.1 i
  let Pos := { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n }
  letI : Fintype Pos := Fintype.ofEquiv { x : B // P x } (positiveSubtypeEquiv n d)
  have h_antidiag_to_B :
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
        ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
    calc
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
          ∑ a : A, ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g := by
        simpa [A] using (Finset.sum_attach A
          (fun a : ℕ →₀ ℕ => ∏ i ∈ Finset.range d, PowerSeries.coeff (a i) g)).symm
      _ = ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
        exact Fintype.sum_equiv (finsuppAntidiagRangeEquivFin n d)
          (fun a : A => ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g)
          (fun l : B => ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
          (by
            intro a
            calc
              (∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g) =
                  ∏ i : Fin d, PowerSeries.coeff (a.1 i.val) g := by
                exact (Fin.prod_univ_eq_prod_range
                  (fun i => PowerSeries.coeff (a.1 i) g) d).symm
              _ = ∏ i : Fin d,
                    PowerSeries.coeff (((finsuppAntidiagRangeEquivFin n d) a).1 i) g := by
                simp [finsuppAntidiagRangeEquivFin])
  rw [h_antidiag_to_B]
  have h_filter :
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
        ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
    have hsubset : (Finset.univ.filter P) ⊆ (Finset.univ : Finset B) := by
      intro x _hx
      simp
    have hsum_subset :
        ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) =
          ∑ x : B, ∏ i : Fin d, PowerSeries.coeff (x.1 i) g := by
      refine Finset.sum_subset hsubset ?_
      intro x _hx hxnot
      exact prod_coeff_eq_zero_of_not_pos hg x (by simpa [P] using hxnot)
    calc
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
          ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) :=
        hsum_subset.symm
      _ = ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
        refine Finset.sum_subtype (Finset.univ.filter P) ?_
          (fun x : B => ∏ i : Fin d, PowerSeries.coeff (x.1 i) g)
        intro x
        simp [P]
  rw [h_filter]
  calc
    (∑ l : { x : B // P x },
        ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g) =
      ∑ l : Pos,
        ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
      exact Fintype.sum_equiv (positiveSubtypeEquiv n d)
        (fun l : { x : B // P x } =>
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (by intro l; rfl)
    _ = ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      exact Fintype.sum_equiv (positiveFinTupleCompositionEquiv n d)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (fun c : { c : Composition n // c.length = d } =>
          ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g)
        (by
          intro l
          change (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
            ∏ i : Fin (List.ofFn l.1).length,
              PowerSeries.coeff ((List.ofFn l.1).get i) g
          exact Fintype.prod_equiv (finCongr (by simp [List.length_ofFn]))
            (fun i : Fin d => PowerSeries.coeff (l.1 i) g)
            (fun i : Fin (List.ofFn l.1).length =>
              PowerSeries.coeff ((List.ofFn l.1).get i) g)
            (by intro i; simp))

private lemma subst_coeff_eq_sum_composition {f g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
  classical
  have hsubst := PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg) f n
  rw [hsubst]
  simp only [smul_eq_mul]
  let term : ℕ → ℂ := fun d => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)
  have hsupport : Function.support term ⊆ (Finset.range (n + 1) : Set ℕ) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hmem
    have hnd : n < d := by omega
    have hz : PowerSeries.coeff n (g ^ d) = 0 :=
      coeff_pow_eq_zero_of_constantCoeff_eq_zero hg hnd
    have hdne : term d ≠ 0 := hd
    simp [term, hz] at hdne
  calc
    (∑ᶠ d : ℕ, PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) =
        ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) := by
      simpa [term] using finsum_eq_sum_of_support_subset term hsupport
    _ = ∑ d ∈ Finset.range (n + 1),
        ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      refine Finset.sum_congr rfl ?_
      intro d _hd
      rw [coeff_pow_eq_sum_composition_length hg d n]
      simp [Finset.mul_sum]
    _ = ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun d => ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g) (n + 1)]
      rw [← Fintype.sum_sigma (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
        PowerSeries.coeff x.1.val f *
          ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)]
      exact Fintype.sum_equiv (sigmaLengthCompositionEquiv n)
        (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
          PowerSeries.coeff x.1.val f *
            ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)
        (fun c : Composition n =>
          PowerSeries.coeff c.length f *
            ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g)
        (by
          intro x
          rcases x with ⟨d, c, hc⟩
          dsimp [sigmaLengthCompositionEquiv]
          apply congrArg₂ HMul.hMul
          · exact congrArg (fun k => PowerSeries.coeff k f) hc.symm
          · rfl)

namespace PowerSeries

theorem toFMLS_subst_eq_comp {f g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.toFMLS (f.subst g) =
      (PowerSeries.toFMLS f).comp (PowerSeries.toFMLS g) := by
  ext n
  simp [PowerSeries.coeff_toFMLS]
  change PowerSeries.coeff n (f.subst g) =
    ((FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n f)).comp
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n g))).coeff n
  rw [FormalMultilinearSeries.ofScalars_comp_coeff]
  exact subst_coeff_eq_sum_composition hg n

end PowerSeries
end

open Filter Asymptotics
open scoped BigOperators ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic

private lemma closedBall_subset_eball_of_ofReal_lt_radius
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hRrad : ENNReal.ofReal R < p.radius) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.eball (0 : ℂ) p.radius := by
  intro z hz
  have hdist : dist z (0 : ℂ) ≤ R := by
    simpa [Metric.mem_closedBall] using hz
  have hed : edist z (0 : ℂ) ≤ ENNReal.ofReal R := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist
  exact hed.trans_lt hRrad

private lemma exists_norm_bound_on_sphere
    {g : ℂ → ℂ} {R : ℝ}
    (hg : ContinuousOn g (Metric.sphere (0 : ℂ) R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g z‖ ≤ M := by
  have hnorm : ContinuousOn (fun z : ℂ => ‖g z‖) (Metric.sphere (0 : ℂ) R) :=
    continuous_norm.comp_continuousOn hg
  have hbdd :
      BddAbove ((fun z : ℂ => ‖g z‖) '' Metric.sphere (0 : ℂ) R) :=
    (isCompact_sphere (0 : ℂ) R).bddAbove_image hnorm
  rcases hbdd with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hM (Set.mem_image_of_mem (fun z : ℂ => ‖g z‖) hz)).trans (le_max_left _ _)

/-- Cauchy's coefficient estimate on a circle gives geometric decay for the coefficients of an
analytic remainder on the closed disk. -/
theorem coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
    {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt g p 0)
    (hd : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) R)) :
    (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hcont_closed : ContinuousOn g (Metric.closedBall (0 : ℂ) R) :=
    hd.continuousOn
  have hcont_sphere : ContinuousOn g (Metric.sphere (0 : ℂ) R) :=
    hcont_closed.mono Metric.sphere_subset_closedBall
  rcases exists_norm_bound_on_sphere (g := g) (R := R) hcont_sphere with
    ⟨M, hM_nonneg, hM⟩
  have hcoeff : ∀ n : ℕ, ‖p.coeff n‖ ≤ M * R⁻¹ ^ n := by
    intro n
    exact norm_coeff_le_of_circleIntegral hR hp hd hM n
  refine isBigO_of_le' (l := atTop) (c := M) ?_
  intro n
  have hpow_nonneg : 0 ≤ R⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hR.le) n
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (p.coeff n)),
    abs_of_nonneg hpow_nonneg, abs_of_nonneg hR.le] using hcoeff n

/-- Radius form of the analytic-remainder estimate for a formal power series. -/
theorem coeff_norm_isBigO_of_radius
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R) (hRrad : ENNReal.ofReal R < p.radius) :
    (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hpos : 0 < p.radius :=
    (ENNReal.ofReal_pos.mpr hR).trans hRrad
  have hpball : HasFPowerSeriesOnBall p.sum p (0 : ℂ) p.radius :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall p hpos
  have hd_eball : DifferentiableOn ℂ p.sum (Metric.eball (0 : ℂ) p.radius) :=
    hpball.differentiableOn
  have hd_closed : DifferentiableOn ℂ p.sum (Metric.closedBall (0 : ℂ) R) :=
    hd_eball.mono (closedBall_subset_eball_of_ofReal_lt_radius (p := p) hRrad)
  exact coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn hR
    hpball.hasFPowerSeriesAt hd_closed

/-- Radius form specialized to the project's `PowerSeries.toFMLS` bridge. -/
theorem powerSeries_coeff_norm_isBigO_of_radius
    (g : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R) (hRrad : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius) :
    (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n g‖) =O[atTop]
      (fun n : ℕ => R⁻¹ ^ n) := by
  simpa using coeff_norm_isBigO_of_radius
    (p := PowerSeries.toFMLS g) hR hRrad

/-- If a power series is a finite simple-pole sum plus a remainder analytic past `R`, then the
coefficient error after subtracting the principal part is geometrically small. -/
theorem coeff_sub_principalPart_isBigO_of_remainder_radius
    (f S g : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R) (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg : f = S + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
      PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hgO :
      (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n g‖) =O[atTop]
        (fun n : ℕ => R⁻¹ ^ n) :=
    powerSeries_coeff_norm_isBigO_of_radius g hR hgR
  have hgO_complex :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n g) =O[atTop]
        (fun n : ℕ => R⁻¹ ^ n) :=
    IsBigO.of_norm_left hgO
  have hcoeff :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =ᶠ[atTop]
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n g) := by
    exact Eventually.of_forall fun n => by
      rw [hfg]
      simp
  exact hcoeff.trans_isBigO hgO_complex

private lemma inv_lt_inv_of_pos_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    y⁻¹ < x⁻¹ := by
  simpa [one_div] using one_div_lt_one_div_of_lt hx hxy

private lemma inv_radius_pow_isLittleO_simplePole
    {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0) :
    (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  have hR : 0 < R := hρ.trans hρR
  have hinv_lt : R⁻¹ < ‖ρ‖⁻¹ :=
    inv_lt_inv_of_pos_lt hρ hρR
  have hpowLittle :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) :=
    isLittleO_pow_pow_of_lt_left (inv_nonneg.mpr hR.le) hinv_lt
  have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hρnorm : ‖ρ‖ ≠ 0 := ne_of_gt hρ
  have hpowOmain :
      (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) =O[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
    refine isBigO_of_le' (l := atTop) (c := (‖c‖ * ‖ρ‖⁻¹)⁻¹) ?_
    intro n
    have hbase_nonneg : 0 ≤ ‖ρ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ρ)
    have hpow_nonneg : 0 ≤ ‖ρ‖⁻¹ ^ n := pow_nonneg hbase_nonneg n
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    apply le_of_eq
    calc
      ‖ρ‖⁻¹ ^ n =
          (‖c‖ * ‖ρ‖⁻¹)⁻¹ * (‖c‖ * (‖ρ‖⁻¹ ^ (n + 1))) := by
        rw [pow_succ]
        field_simp [hcnorm, hρnorm]
      _ = (‖c‖ * ‖ρ‖⁻¹)⁻¹ * ‖c * ρ⁻¹ ^ (n + 1)‖ := by
        rw [norm_mul, norm_pow, norm_inv]
  exact hpowLittle.trans_isBigO hpowOmain

/-- The single-pole principal part with pole at `ρ` has coefficients
`c * (ρ⁻¹)^(n+1)`, matching the normalization of
`PowerSeries.coeff_simplePoleSum`. -/
theorem single_simplePole_principal_isEquivalent
    {ρ c : ℂ} :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (PowerSeries.C (c * ρ⁻¹) *
        PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)))) ~[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  apply Filter.EventuallyEq.isEquivalent
  exact Eventually.of_forall fun n => by
    calc
      PowerSeries.coeff (R := ℂ) n
          (PowerSeries.C (c * ρ⁻¹) *
            PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))) =
          (c * ρ⁻¹) * ρ⁻¹ ^ n := by
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale_invUnitsSub_one]
      _ = c * ρ⁻¹ ^ (n + 1) := by
        rw [pow_succ]
        ring

/-- Dominant simple pole transfer: a single simple pole at `ρ` plus a remainder analytic past `R`
has coefficients asymptotic to the pole contribution. -/
theorem dominant_simplePole_isEquivalent
    (f g : PowerSeries ℂ) {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg :
      f =
        PowerSeries.C (c * ρ⁻¹) *
          PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)) + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f) ~[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  let S : PowerSeries ℂ :=
    PowerSeries.C (c * ρ⁻¹) *
      PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))
  have hR : 0 < R := hρ.trans hρR
  have hremO :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) :=
    coeff_sub_principalPart_isBigO_of_remainder_radius f S g hR hgR hfg
  have hgeom :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    inv_radius_pow_isLittleO_simplePole hρ hρR hc
  have hremLittle :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =o[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    hremO.trans_isLittleO hgeom
  have hS :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n S) ~[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
    simpa [S] using single_simplePole_principal_isEquivalent
      (ρ := ρ) (c := c)
  have hsum :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n S +
        (PowerSeries.coeff (R := ℂ) n f - PowerSeries.coeff (R := ℂ) n S)) ~[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    hS.add_isLittleO hremLittle
  exact hsum.congr_left (Eventually.of_forall fun n => by ring)

end Meromorphic
end Ch5
end AnalyticCombinatorics
end

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Surjections

open AnalyticCombinatorics.Ch1

lemma rho_im : rho.im = 0 := by
  exact Complex.ofReal_im (Real.log 2)

lemma real_log_two_pos : 0 < Real.log 2 := by
  exact Real.log_pos (by norm_num)

lemma rho_ne_zero : rho ≠ 0 := by
  rw [rho]
  exact_mod_cast (ne_of_gt real_log_two_pos)

lemma rho_norm : ‖rho‖ = Real.log 2 := by
  rw [rho]
  rw [Complex.norm_of_nonneg real_log_two_pos.le]

lemma rho_norm_pos : 0 < ‖rho‖ := by
  rw [rho_norm]
  exact real_log_two_pos

lemma rho_norm_lt_one : ‖rho‖ < 1 := by
  rw [rho_norm]
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  norm_num at h
  exact h

lemma half_ne_zero : (1 / 2 : ℂ) ≠ 0 := by
  norm_num

theorem surjEGFℂ_mul_denominator :
    surjEGFℂ * (1 - (PowerSeries.exp ℂ - 1)) = 1 := by
  have h := congrArg PowerSeries.mapℂ CombClass.egf_surjections
  simpa [surjEGFℂ, PowerSeries.mapℂ] using h

theorem surjEGFℂ_eq_inv_denominator :
    surjEGFℂ = (1 - (PowerSeries.exp ℂ - 1))⁻¹ := by
  have h0 : PowerSeries.constantCoeff (1 - (PowerSeries.exp ℂ - 1) : PowerSeries ℂ) ≠ 0 := by
    simp
  exact (PowerSeries.eq_inv_iff_mul_eq_one h0).2 surjEGFℂ_mul_denominator

theorem surjEGFℂ_eq_principal_add_remainder :
    surjEGFℂ = principal + remainder := by
  unfold remainder
  abel

lemma coeff_principal (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n principal = (1 / 2 : ℂ) * rho⁻¹ ^ (n + 1) := by
  rw [principal, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale_invUnitsSub_one]
  rw [pow_succ]
  ring

theorem coeff_surjEGFℂ_isEquivalent_of_remainder_radius
    (hrem : ENNReal.ofReal (1 : ℝ) < (PowerSeries.toFMLS remainder).radius) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n surjEGFℂ)
      ~[atTop] (fun n : ℕ => (1 / 2 : ℂ) * rho⁻¹ ^ (n + 1)) := by
  exact dominant_simplePole_isEquivalent
    surjEGFℂ remainder (ρ := rho) (c := (1 / 2 : ℂ)) (R := 1)
    rho_norm_pos rho_norm_lt_one half_ne_zero hrem surjEGFℂ_eq_principal_add_remainder

lemma expMinusOne_constantCoeff :
    PowerSeries.constantCoeff (PowerSeries.exp ℂ - 1 : PowerSeries ℂ) = 0 := by
  simp

theorem surjEGFℂ_eq_geometric_subst :
    surjEGFℂ =
      (PowerSeries.invUnitsSub (1 : ℂˣ)).subst (PowerSeries.exp ℂ - 1) := by
  set_option backward.isDefEq.respectTransparency false in
    let H : PowerSeries ℂ := PowerSeries.exp ℂ - 1
    have hH0 : PowerSeries.constantCoeff H = 0 := by
      simp [H]
    have hsubst : (PowerSeries.invUnitsSub (1 : ℂˣ)).subst H * (1 - H) = 1 := by
      have hHas : PowerSeries.HasSubst H := PowerSeries.HasSubst.of_constantCoeff_zero hH0
      have hsubHX :
          (PowerSeries.C ((1 : ℂˣ) : ℂ) - PowerSeries.X).subst H = 1 - H := by
        rw [← PowerSeries.coe_substAlgHom hHas, map_sub,
          PowerSeries.substAlgHom_X hHas]
        simp
      rw [← hsubHX, ← PowerSeries.subst_mul hHas, PowerSeries.invUnitsSub_mul_sub]
      change (PowerSeries.C (1 : ℂ)).subst H = 1
      rw [← PowerSeries.coe_substAlgHom hHas]
      simp
    rw [surjEGFℂ_eq_inv_denominator]
    have h0 : PowerSeries.constantCoeff (1 - H : PowerSeries ℂ) ≠ 0 := by
      simp [H]
    exact ((PowerSeries.eq_inv_iff_mul_eq_one h0).2 hsubst).symm

lemma toFMLS_invUnitsSub_one :
    PowerSeries.toFMLS (PowerSeries.invUnitsSub (1 : ℂˣ)) =
      formalMultilinearSeries_geometric ℂ ℂ := by
  ext n
  simp [PowerSeries.toFMLS, formalMultilinearSeries_geometric_eq_ofScalars,
    FormalMultilinearSeries.ofScalars]

lemma toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_one :
    PowerSeries.toFMLS (1 : PowerSeries ℂ) =
      constFormalMultilinearSeries ℂ ℂ (1 : ℂ) := by
  ext n
  cases n with
  | zero =>
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        constFormalMultilinearSeries]
  | succ n =>
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        constFormalMultilinearSeries]

lemma toFMLS_powerSeries_exp :
    PowerSeries.toFMLS (PowerSeries.exp ℂ) = NormedSpace.expSeries ℂ ℂ := by
  rw [NormedSpace.expSeries_eq_ofScalars]
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_expMinusOne :
    PowerSeries.toFMLS (PowerSeries.exp ℂ - 1) =
      NormedSpace.expSeries ℂ ℂ - constFormalMultilinearSeries ℂ ℂ (1 : ℂ) := by
  rw [toFMLS_sub, toFMLS_powerSeries_exp, toFMLS_one]

lemma complex_exp_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp (NormedSpace.expSeries ℂ ℂ) (0 : ℂ) := by
  simpa [Complex.exp_eq_exp_ℂ] using
    (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℂ) (𝔸 := ℂ))

lemma complex_exp_analyticAt (z : ℂ) : AnalyticAt ℂ Complex.exp z := by
  simpa [Complex.exp_eq_exp_ℂ] using
    (NormedSpace.exp_analytic (𝕂 := ℂ) (𝔸 := ℂ) z)

lemma expSubOne_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt expSubOne
      (NormedSpace.expSeries ℂ ℂ - constFormalMultilinearSeries ℂ ℂ (1 : ℂ)) (0 : ℂ) := by
  simpa [expSubOne, Pi.sub_apply] using
    complex_exp_hasFPowerSeriesAt_zero.sub
      (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
        (c := (1 : ℂ)) (e := (0 : ℂ)))

theorem surjAnalyticFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt surjAnalyticFun (PowerSeries.toFMLS surjEGFℂ) (0 : ℂ) := by
  have houter : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (0 : ℂ) :=
    (hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ).hasFPowerSeriesAt
  have houter' : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (expSubOne 0) := by
    simpa [expSubOne] using houter
  have hcomp := houter'.comp expSubOne_hasFPowerSeriesAt_zero
  rw [surjEGFℂ_eq_geometric_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp expMinusOne_constantCoeff]
  rw [toFMLS_invUnitsSub_one, toFMLS_expMinusOne]
  refine hcomp.congr ?_
  filter_upwards with z
  set_option backward.isDefEq.respectTransparency false in
    simp [surjAnalyticFun, expSubOne]
    ring_nf

theorem principalAnalyticFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt principalAnalyticFun (PowerSeries.toFMLS principal) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) rho_norm_pos] with z hz
  have hz_norm : ‖z‖ < ‖rho‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hzr : ‖z * rho⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv]
    have hpos : 0 < ‖rho‖⁻¹ := inv_pos.mpr rho_norm_pos
    calc
      ‖z‖ * ‖rho‖⁻¹ < ‖rho‖ * ‖rho‖⁻¹ :=
        mul_lt_mul_of_pos_right hz_norm hpos
      _ = 1 := by
        field_simp [ne_of_gt rho_norm_pos]
  have hlin_ne : 1 - z * rho⁻¹ ≠ 0 := by
    intro h
    have hzreq : z * rho⁻¹ = 1 := (sub_eq_zero.mp h).symm
    have hnorm : ‖z * rho⁻¹‖ = 1 := by
      rw [hzreq, norm_one]
    linarith
  have hrz_ne : rho - z ≠ 0 := by
    intro h
    have hzrho : rho = z := sub_eq_zero.mp h
    have hnorm : ‖z‖ = ‖rho‖ := by
      rw [← hzrho]
    linarith
  have hsum :
      HasSum (fun n : ℕ => ((1 / 2 : ℂ) * rho⁻¹) * (z * rho⁻¹) ^ n)
        (((1 / 2 : ℂ) * rho⁻¹) * (1 - z * rho⁻¹)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hzr).mul_left ((1 / 2 : ℂ) * rho⁻¹)
  convert hsum using 1
  · ext n
    rw [PowerSeries.coeff_toFMLS, coeff_principal]
    simp [smul_eq_mul]
    rw [pow_succ, mul_pow]
    ring
  · simp [principalAnalyticFun]
    field_simp [rho_ne_zero, hlin_ne, hrz_ne]

lemma expDiv_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt expDiv
      (NormedSpace.expSeries ℂ ℂ - constFormalMultilinearSeries ℂ ℂ (1 : ℂ)).fslope
      (0 : ℂ) := by
  simpa [expDiv] using expSubOne_hasFPowerSeriesAt_zero.has_fpower_series_dslope_fslope

lemma expDiv_analyticAt_zero : AnalyticAt ℂ expDiv (0 : ℂ) :=
  expDiv_hasFPowerSeriesAt_zero.analyticAt

lemma expDiv_of_ne {z : ℂ} (hz : z ≠ 0) :
    expDiv z = z⁻¹ * (Complex.exp z - 1) := by
  rw [expDiv, dslope_of_ne expSubOne hz]
  simp [expSubOne, slope_def_module, smul_eq_mul]

lemma expDiv_zero : expDiv 0 = 1 := by
  rw [expDiv, dslope_same]
  change deriv expSubOne (0 : ℂ) = 1
  rw [show expSubOne = fun z : ℂ => Complex.exp z - 1 by rfl]
  rw [deriv_sub_const]
  rw [Complex.deriv_exp]
  simp

lemma expDiv_analyticAt_of_ne {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ expDiv z := by
  have hmodel : AnalyticAt ℂ (fun w : ℂ => w⁻¹ * (Complex.exp w - 1)) z :=
    (analyticAt_id.inv hz).mul
      ((complex_exp_analyticAt z).sub
        (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := z)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne expSubOne hz).mono fun w hw => by
    simpa [expDiv, expSubOne, slope_def_module, smul_eq_mul] using hw.symm

lemma expDiv_analyticAt (z : ℂ) : AnalyticAt ℂ expDiv z := by
  by_cases hz : z = 0
  · simpa [hz] using expDiv_analyticAt_zero
  · exact expDiv_analyticAt_of_ne hz

lemma expDivSlope_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt expDivSlope
      ((NormedSpace.expSeries ℂ ℂ - constFormalMultilinearSeries ℂ ℂ (1 : ℂ)).fslope.fslope)
      (0 : ℂ) := by
  simpa [expDivSlope] using expDiv_hasFPowerSeriesAt_zero.has_fpower_series_dslope_fslope

lemma expDivSlope_analyticAt_zero : AnalyticAt ℂ expDivSlope (0 : ℂ) :=
  expDivSlope_hasFPowerSeriesAt_zero.analyticAt

lemma expDivSlope_of_ne {z : ℂ} (hz : z ≠ 0) :
    expDivSlope z = z⁻¹ * (expDiv z - 1) := by
  rw [expDivSlope, dslope_of_ne expDiv hz]
  simp [slope_def_module, expDiv_zero, smul_eq_mul]

lemma expDivSlope_analyticAt_of_ne {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ expDivSlope z := by
  have hmodel : AnalyticAt ℂ (fun w : ℂ => w⁻¹ * (expDiv w - 1)) z :=
    (analyticAt_id.inv hz).mul
      ((expDiv_analyticAt z).sub
        (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := z)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne expDiv hz).mono fun w hw => by
    simpa [expDivSlope, slope_def_module, expDiv_zero, smul_eq_mul] using hw.symm

lemma expDivSlope_analyticAt (z : ℂ) : AnalyticAt ℂ expDivSlope z := by
  by_cases hz : z = 0
  · simpa [hz] using expDivSlope_analyticAt_zero
  · exact expDivSlope_analyticAt_of_ne hz

lemma exp_rho : Complex.exp rho = 2 := by
  rw [rho, ← Complex.ofReal_exp]
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

lemma eq_rho_of_exp_eq_two_of_norm_le_two {z : ℂ}
    (hz_norm : ‖z‖ ≤ 2) (hz_exp : Complex.exp z = 2) :
    z = rho := by
  have hz_exp_rho : Complex.exp z = Complex.exp rho := by
    simpa [exp_rho] using hz_exp
  rcases (Complex.exp_eq_exp_iff_exists_int).mp hz_exp_rho with ⟨k, hk⟩
  by_cases hk0 : k = 0
  · simpa [hk0] using hk
  · exfalso
    have hz_im : z.im = (k : ℝ) * (2 * Real.pi) := by
      calc
        z.im = (rho + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im := by
          rw [hk]
        _ = rho.im + ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im := by
          rw [Complex.add_im]
        _ = 0 + ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im := by
          rw [rho_im]
        _ = (k : ℝ) * (2 * Real.pi) := by
          simp [Complex.mul_im]
    have him_le_norm : |(k : ℝ) * (2 * Real.pi)| ≤ ‖z‖ := by
      rw [← hz_im]
      exact Complex.abs_im_le_norm z
    have hkabs_int : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
      exact_mod_cast hkabs_int
    have htwopi_nonneg : 0 ≤ 2 * Real.pi := Real.two_pi_pos.le
    have htwopi_le : 2 * Real.pi ≤ |(k : ℝ) * (2 * Real.pi)| := by
      rw [abs_mul, abs_of_nonneg htwopi_nonneg]
      nlinarith [hkabs, Real.two_pi_pos]
    have htwo_lt_twopi : (2 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    linarith

lemma expDiv_ne_zero_on_closedBall_two {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
    expDiv (z - rho) ≠ 0 := by
  intro hzero
  by_cases hw : z - rho = 0
  · have hval : expDiv (z - rho) = 1 := by simpa [hw] using expDiv_zero
    rw [hval] at hzero
    exact one_ne_zero hzero
  · have hexpw : Complex.exp (z - rho) = 1 := by
      have hdiv := hzero
      rw [expDiv_of_ne hw] at hdiv
      have hsub : Complex.exp (z - rho) - 1 = 0 :=
        (mul_eq_zero.mp hdiv).resolve_left (inv_ne_zero hw)
      exact sub_eq_zero.mp hsub
    have hz_exp : Complex.exp z = 2 := by
      have hzsplit : z = rho + (z - rho) := by abel
      rw [hzsplit, Complex.exp_add, exp_rho, hexpw]
      norm_num
    have hz_norm : ‖z‖ ≤ 2 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzrho := eq_rho_of_exp_eq_two_of_norm_le_two hz_norm hz_exp
    exact hw (by simp [hzrho])

lemma analyticRemainderFun_analyticAt_on_closedBall_two {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
    AnalyticAt ℂ analyticRemainderFun z := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => w - rho) z :=
    analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := rho) (x := z))
  have hnum : AnalyticAt ℂ (fun w : ℂ => expDivSlope (w - rho)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := expDivSlope) (f := fun w : ℂ => w - rho)
      (x := z) (expDivSlope_analyticAt (z - rho)) hshift
  have hden : AnalyticAt ℂ (fun w : ℂ => expDiv (w - rho)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := expDiv) (f := fun w : ℂ => w - rho)
      (x := z) (expDiv_analyticAt (z - rho)) hshift
  have hquot : AnalyticAt ℂ
      (fun w : ℂ => expDivSlope (w - rho) / expDiv (w - rho)) z :=
    hnum.div hden (expDiv_ne_zero_on_closedBall_two hz)
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) z :=
    analyticAt_const (𝕜 := ℂ) (v := (1 / 2 : ℂ)) (x := z)
  change AnalyticAt ℂ
    (fun w : ℂ => (1 / 2 : ℂ) * (expDivSlope (w - rho) / expDiv (w - rho))) z
  simpa only [Pi.mul_apply] using hconst.mul hquot

theorem analyticRemainderFun_differentiableOn_closedBall_two :
    DifferentiableOn ℂ analyticRemainderFun (Metric.closedBall (0 : ℂ) 2) := by
  intro z hz
  exact (analyticRemainderFun_analyticAt_on_closedBall_two hz).differentiableAt.differentiableWithinAt

lemma analyticRemainderFun_eq_surj_sub_principal {z : ℂ}
    (hz : z - rho ≠ 0) (hdiv : expDiv (z - rho) ≠ 0) :
    analyticRemainderFun z = surjAnalyticFun z - principalAnalyticFun z := by
  have h_exp_sub_ne : Complex.exp (z - rho) - 1 ≠ 0 := by
    intro h
    apply hdiv
    rw [expDiv_of_ne hz, h]
    simp
  have h_one_sub_exp_ne : 1 - Complex.exp (z - rho) ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using neg_ne_zero.mpr h_exp_sub_ne
  have h_surj_den_ne : 2 - 2 * Complex.exp (z - rho) ≠ 0 := by
    intro h
    have hfactor : (2 : ℂ) * (1 - Complex.exp (z - rho)) = 0 := by
      simpa [mul_sub] using h
    rcases mul_eq_zero.mp hfactor with htwo | hone
    · exact (by norm_num : (2 : ℂ) ≠ 0) htwo
    · exact h_one_sub_exp_ne hone
  have h_rho_sub_ne : rho - z ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using neg_ne_zero.mpr hz
  have h_exp : Complex.exp z = 2 * Complex.exp (z - rho) := by
    have hzsplit : z = rho + (z - rho) := by abel
    calc
      Complex.exp z = Complex.exp (rho + (z - rho)) := congrArg Complex.exp hzsplit
      _ = Complex.exp rho * Complex.exp (z - rho) := by rw [Complex.exp_add]
      _ = 2 * Complex.exp (z - rho) := by rw [exp_rho]
  rw [analyticRemainderFun, surjAnalyticFun, principalAnalyticFun]
  rw [expDivSlope_of_ne hz, expDiv_of_ne hz, h_exp]
  field_simp [hz, hdiv, h_exp_sub_ne, h_one_sub_exp_ne, h_surj_den_ne, h_rho_sub_ne]
  ring

theorem analyticRemainderFun_eventually_eq_surj_sub_principal :
    (fun z : ℂ => surjAnalyticFun z - principalAnalyticFun z)
      =ᶠ[𝓝 (0 : ℂ)] analyticRemainderFun := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) rho_norm_pos] with z hz
  have hz_norm : ‖z‖ < ‖rho‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz_closed_two : z ∈ Metric.closedBall (0 : ℂ) 2 := by
    have hz_two : ‖z‖ ≤ 2 := by
      have hlt_one : ‖z‖ < 1 := hz_norm.trans rho_norm_lt_one
      linarith
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz_two
  have hz_ne : z - rho ≠ 0 := by
    intro h
    have hzrho : z = rho := sub_eq_zero.mp h
    have hnorm : ‖z‖ = ‖rho‖ := by rw [hzrho]
    linarith
  exact (analyticRemainderFun_eq_surj_sub_principal hz_ne
    (expDiv_ne_zero_on_closedBall_two hz_closed_two)).symm

lemma toFMLS_remainder :
    PowerSeries.toFMLS remainder =
      PowerSeries.toFMLS surjEGFℂ - PowerSeries.toFMLS principal := by
  rw [remainder, toFMLS_sub]

theorem analyticRemainderFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt analyticRemainderFun (PowerSeries.toFMLS remainder) (0 : ℂ) := by
  have hsub := surjAnalyticFun_hasFPowerSeriesAt_zero.sub
    principalAnalyticFun_hasFPowerSeriesAt_zero
  have hsub' : HasFPowerSeriesAt
      (fun z : ℂ => surjAnalyticFun z - principalAnalyticFun z)
      (PowerSeries.toFMLS remainder) (0 : ℂ) := by
    simpa [toFMLS_remainder] using hsub
  exact hsub'.congr analyticRemainderFun_eventually_eq_surj_sub_principal

theorem remainder_radius_gt_one :
    ENNReal.ofReal (1 : ℝ) < (PowerSeries.toFMLS remainder).radius := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS remainder
  have hcoeffO :
      (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) :=
    coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
      (g := analyticRemainderFun) (p := p) (R := 2)
      (by norm_num) analyticRemainderFun_hasFPowerSeriesAt_zero
      analyticRemainderFun_differentiableOn_closedBall_two
  have hcancel :
      (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n) * (2 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have hpow : ((2 : ℝ)⁻¹ ^ n) * (2 : ℝ) ^ n = 1 := by
      set_option backward.isDefEq.respectTransparency false in
        rw [← mul_pow]
        norm_num
    rw [hpow]
    norm_num
  have hcoeffMul :
      (fun n : ℕ => ‖p.coeff n‖ * (2 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    exact (hcoeffO.mul (isBigO_refl (fun n : ℕ => (2 : ℝ) ^ n) atTop)).trans hcancel
  have hnorm_eq :
      (fun n : ℕ => ‖p n‖ * (2 : ℝ) ^ n) =ᶠ[atTop]
        (fun n : ℕ => ‖p.coeff n‖ * (2 : ℝ) ^ n) := by
    exact Eventually.of_forall fun n => by
      have hpn : ‖p n‖ = ‖p.coeff n‖ := by
        simp [p, PowerSeries.toFMLS]
      change ‖p n‖ * (2 : ℝ) ^ n = ‖p.coeff n‖ * (2 : ℝ) ^ n
      rw [hpn]
  have hterm :
      (fun n : ℕ => ‖p n‖ * (2 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    hnorm_eq.trans_isBigO hcoeffMul
  have hle : ((2 : ℝ≥0) : ℝ≥0∞) ≤ p.radius :=
    p.le_radius_of_isBigO (r := (2 : ℝ≥0)) hterm
  have hone_two : ENNReal.ofReal (1 : ℝ) < ((2 : ℝ≥0) : ℝ≥0∞) := by
    norm_num
  exact hone_two.trans_le hle

theorem coeff_surjEGFℂ_isEquivalent :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n surjEGFℂ)
      ~[atTop] (fun n : ℕ => (1 : ℂ) / (2 * rho ^ (n + 1))) := by
  have hmain := coeff_surjEGFℂ_isEquivalent_of_remainder_radius remainder_radius_gt_one
  refine hmain.trans_eventuallyEq (Eventually.of_forall fun n => ?_)
  calc
    (1 / 2 : ℂ) * rho⁻¹ ^ (n + 1) =
        (1 / 2 : ℂ) * (rho ^ (n + 1))⁻¹ := by
      rw [inv_pow]
    _ = (1 : ℂ) / (2 * rho ^ (n + 1)) := by
      change (1 : ℂ) * 2⁻¹ * (rho ^ (n + 1))⁻¹ =
        (1 : ℂ) * (2 * rho ^ (n + 1))⁻¹
      rw [mul_inv_rev]
      ring

end Surjections
end Meromorphic
end Ch5
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch5 AnalyticCombinatorics.Ch5.Meromorphic AnalyticCombinatorics.Ch5.Meromorphic.Surjections
open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology
open AnalyticCombinatorics.Ch1
theorem solution :
    (fun n : ℕ =>
      algebraMap ℚ ℂ ((surjectionsCount n : ℚ) / (n.factorial : ℚ)))
      ~[atTop]
    (fun n : ℕ => (1 : ℂ) / (2 * (((Real.log 2 : ℝ) : ℂ) ^ (n + 1)))) := by
  have hbridge :
      (fun n : ℕ =>
        algebraMap ℚ ℂ ((surjectionsCount n : ℚ) / (n.factorial : ℚ)))
        =ᶠ[atTop]
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n surjEGFℂ) := by
    exact Eventually.of_forall fun n => by
      change algebraMap ℚ ℂ
          ((CombClass.posInt.lseq.counts n : ℚ) / (n.factorial : ℚ)) =
        PowerSeries.coeff (R := ℂ) n surjEGFℂ
      rw [surjEGFℂ, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
  exact hbridge.trans_isEquivalent (by simpa [rho] using coeff_surjEGFℂ_isEquivalent)
