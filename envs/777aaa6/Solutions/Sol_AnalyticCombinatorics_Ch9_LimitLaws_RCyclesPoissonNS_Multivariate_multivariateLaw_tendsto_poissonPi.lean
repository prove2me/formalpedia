-- Prove2me | solution 1 for AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Multivariate.multivariateLaw_tendsto_poissonPi
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T18:49:12.161425+00:00
-- url     : https://prove2.me/submissions/a2355947-1e83-484d-9ea2-b3e906d09255

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesFactorialMoment
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_JointCycleMoments
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_MultivariateCyclePoisson
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Cycles of a fixed length in a random permutation

This file sets up the genuine random variable counting cycles of length exactly
`r` in a uniform random permutation of `Fin n`.

For `r = 1` this is the fixed-point count.  For `r ≥ 2` it is the multiplicity
of `r` in Mathlib's `cycleType`, equivalently the number of nontrivial cycle
factors with support of cardinality `r`.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

@[simp]
lemma rCycleCount_one (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n 1 σ = FixedPointsPoissonNS.fixedPointCount n σ := by
  simp [rCycleCount]

lemma rCycleCount_eq_cycleType_count_of_ne_one {n r : ℕ}
    (hr : r ≠ 1) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ = σ.cycleType.count r := by
  simp [rCycleCount, hr]

lemma poisson_law_singleton (r : ℝ≥0) (j : ℕ) :
    (ProbabilityTheory.poissonMeasure r) ({j} : Set ℕ) =
      ENNReal.ofReal (ProbabilityTheory.poissonPMFReal r j) := by
  rw [ProbabilityTheory.poissonMeasure]
  exact PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

/-!
# Factorial moments for fixed-length cycles

This file records unconditional finite-average identities for the genuine
`rCycleCount` random variable from `RCyclesPoisson.lean`.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

namespace FM

section GeneralFinite

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma cycleType_singleton_iff_in {r : ℕ} {c : Equiv.Perm α} :
    c.cycleType = ({r} : Multiset ℕ) ↔ c.IsCycle ∧ c.support.card = r := by
  constructor
  · intro h
    have hc : c.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one]
      rw [h]
      simp
    refine ⟨hc, ?_⟩
    have hsum := c.sum_cycleType
    rw [h] at hsum
    simpa using hsum.symm
  · rintro ⟨hc, hcard⟩
    rw [hc.cycleType, hcard]

lemma card_cyclesOfLengthIn {r : ℕ} (hr : 2 ≤ r) (hrα : r ≤ Fintype.card α) :
    Fintype.card (CyclesOfLengthIn (α := α) r) =
      (r - 1).factorial * (Fintype.card α).choose r := by
  classical
  have hcycles := Equiv.Perm.card_of_cycleType_singleton
    (α := α) (n := r) hr hrα
  have hsub :
      Fintype.card (CyclesOfLengthIn (α := α) r) =
        ({g | g.cycleType = ({r} : Multiset ℕ)} : Finset (Equiv.Perm α)).card := by
    change Fintype.card {c : Equiv.Perm α // c.IsCycle ∧ c.support.card = r} =
      ({g | g.cycleType = ({r} : Multiset ℕ)} : Finset (Equiv.Perm α)).card
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext g
    simp [cycleType_singleton_iff_in]
  rw [hsub, hcycles]

lemma card_cyclesOfLengthOfPermIn {r : ℕ} (σ : Equiv.Perm α) :
    Fintype.card (CyclesOfLengthOfPermIn (α := α) r σ) = σ.cycleType.count r := by
  classical
  rw [Equiv.Perm.CycleType.count_def (σ := σ) r]
  rfl

lemma card_complement_cycle_support_in {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support} =
      Fintype.card α - r := by
  classical
  rw [Fintype.card_subtype_compl (fun x : α => x ∈ (c : Equiv.Perm α).support)]
  rw [Fintype.card_coe, c.prop.2]

lemma cycleType_count_containing_from_complement {r k : ℕ}
    (c : CyclesOfLengthIn (α := α) r)
    (τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support}) :
    ((((permComplementEquivContainingCycleIn c) τ).1.cycleType.count r - 1).descFactorial k) =
      (τ.cycleType.count r).descFactorial k := by
  classical
  dsimp [permComplementEquivContainingCycleIn, permDisjointCycleEquivComplementIn,
    permContainingCycleEquivDisjointCycleIn]
  have hctype : (c : Equiv.Perm α).cycleType = ({r} : Multiset ℕ) :=
    cycleType_singleton_iff_in.mpr c.prop
  have hdisj :
      Equiv.Perm.Disjoint (Equiv.Perm.ofSubtype τ) (c : Equiv.Perm α) := by
    intro x
    by_cases hx : x ∈ (c : Equiv.Perm α).support
    · exact Or.inl (Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simpa using hx))
    · exact Or.inr (Equiv.Perm.notMem_support.mp hx)
  have hcount :
      ((Equiv.Perm.ofSubtype τ * (c : Equiv.Perm α)).cycleType.count r - 1) =
        τ.cycleType.count r := by
    rw [hdisj.cycleType_mul, hctype, Equiv.Perm.cycleType_ofSubtype]
    simp
  rw [hcount]

lemma descFactorial_succ_eq_mul_pred (m k : ℕ) :
    m.descFactorial (k + 1) = m * (m - 1).descFactorial k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.descFactorial_succ, ih, Nat.descFactorial_succ]
      have hsub : m - (k + 1) = m - 1 - k := by omega
      rw [hsub]
      ring

end GeneralFinite
end FM
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

/-!
# Joint factorial moments for cycle counts

This file starts the mixed factorial-moment theory for cycle counts of
distinct lengths.  The banked result is the exact two-length identity for
nontrivial lengths.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace JointCycleMomentsNS

section GeneralFinite

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma cycleType_count_containing_from_complement_ne {r s : ℕ} (hsr : s ≠ r)
    (c : FM.CyclesOfLengthIn (α := α) r)
    (τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support}) :
    ((FM.permComplementEquivContainingCycleIn c τ).1.cycleType.count s) =
      τ.cycleType.count s := by
  classical
  dsimp [FM.permComplementEquivContainingCycleIn, FM.permDisjointCycleEquivComplementIn,
    FM.permContainingCycleEquivDisjointCycleIn]
  have hctype : (c : Equiv.Perm α).cycleType = ({r} : Multiset ℕ) :=
    FM.cycleType_singleton_iff_in.mpr c.prop
  have hdisj :
      Equiv.Perm.Disjoint (Equiv.Perm.ofSubtype τ) (c : Equiv.Perm α) := by
    intro x
    by_cases hx : x ∈ (c : Equiv.Perm α).support
    · exact Or.inl (Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simpa using hx))
    · exact Or.inr (Equiv.Perm.notMem_support.mp hx)
  rw [hdisj.cycleType_mul, hctype, Equiv.Perm.cycleType_ofSubtype]
  simp [hsr]

lemma card_complement_point (x : α) :
    Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 := by
  rw [Fintype.card_subtype_compl (fun y : α => y = x)]
  rw [Fintype.card_subtype_eq]

lemma cycleType_count_fixingPoint_from_complement {s : ℕ} (x : α)
    (τ : Equiv.Perm {y : α // y ≠ x}) :
    ((permComplementEquivFixingPointIn x τ).1.cycleType.count s) =
      τ.cycleType.count s := by
  dsimp [permComplementEquivFixingPointIn]
  rw [Equiv.Perm.cycleType_ofSubtype]

lemma fixedPointCount_fixingPoint_from_complement_desc {a : ℕ} (x : α)
    (τ : Equiv.Perm {y : α // y ≠ x}) :
    ((fixedPointCountIn ((permComplementEquivFixingPointIn x τ).1) - 1).descFactorial a) =
      (fixedPointCountIn τ).descFactorial a := by
  dsimp [fixedPointCountIn, FixedPointsOfPermIn, permComplementEquivFixingPointIn]
  rw [Equiv.Perm.card_fixedPoints]
  rw [Equiv.Perm.card_fixedPoints]
  rw [Equiv.Perm.cycleType_ofSubtype]
  rw [card_complement_point (α := α) x]
  congr 1
  omega

end GeneralFinite

lemma fixedPointCountIn_fin (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    fixedPointCountIn σ = FixedPointsPoissonNS.fixedPointCount n σ := by
  classical
  unfold fixedPointCountIn FixedPointsOfPermIn FixedPointsPoissonNS.fixedPointCount
  exact Fintype.card_congr
    { toFun := fun x => ⟨x.1, Function.mem_fixedPoints_iff.mp x.2⟩
      invFun := fun x => ⟨x.1, Function.mem_fixedPoints_iff.mpr x.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        rfl
      right_inv := by
        rintro ⟨x, hx⟩
        rfl }

end JointCycleMomentsNS
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

/-!
# Completion of the fixed-length cycle Poisson limit

This file proves the finite Bonferroni/factorial-moment inversion needed to
identify the genuine `r`-cycle pmf with the closed inclusion-exclusion formula.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace Complete

lemma Multiset.count_mul_le_sum (r : ℕ) :
    ∀ s : Multiset ℕ, s.count r * r ≤ s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      by_cases h : a = r
      · subst a
        simp [Nat.succ_mul, Multiset.sum_cons, Nat.add_comm, ih]
      · have hle : s.count r * r ≤ a + s.sum :=
          Nat.le_trans ih (Nat.le_add_left _ _)
        have h' : r ≠ a := fun hra => h hra.symm
        simpa [Multiset.count_cons, h', Multiset.sum_cons] using hle

lemma cycleType_count_mul_le_card {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (σ : Equiv.Perm α) :
    σ.cycleType.count r * r ≤ Fintype.card α := by
  calc
    σ.cycleType.count r * r ≤ σ.cycleType.sum :=
      Multiset.count_mul_le_sum r σ.cycleType
    _ = σ.support.card := Equiv.Perm.sum_cycleType σ
    _ ≤ Fintype.card α := by
      simpa using σ.support.card_le_univ

lemma rCycleCount_mul_le_card {n r : ℕ} (hr : 0 < r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ * r ≤ n := by
  rcases eq_or_ne r 1 with rfl | hrne
  · simpa [rCycleCount, FixedPointsPoissonNS.fixedPointCount, Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => σ i = i)
  · rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    simpa [Fintype.card_fin] using
      cycleType_count_mul_le_card (α := Fin n) r σ

lemma rCycleCount_le_div {n r : ℕ} (hr : 0 < r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ ≤ n / r := by
  exact (Nat.le_div_iff_mul_le hr).2 (rCycleCount_mul_le_card (n := n) (r := r) hr σ)

lemma alternating_choose_sum_range (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ((-1 : ℝ) ^ i * (m.choose i : ℝ))) =
      if m = 0 then 1 else 0 := by
  have h := Int.alternating_sum_range_choose (n := m)
  exact_mod_cast h

lemma alternating_choose_sum_range_of_le {m N : ℕ} (hmN : m ≤ N) :
    (∑ i ∈ Finset.range (N + 1), ((-1 : ℝ) ^ i * (m.choose i : ℝ))) =
      if m = 0 then 1 else 0 := by
  have hsubset : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
    intro i hi
    exact Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.succ_le_succ hmN))
  rw [← alternating_choose_sum_range m]
  exact (Finset.sum_subset hsubset (by
    intro i hiN him
    have hmi : m < i := by
      exact Nat.lt_of_not_ge (fun hi_le_m => him (Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le_m)))
    rw [Nat.choose_eq_zero_of_lt hmi]
    simp)).symm

lemma descFactorial_div_factorials_eq_choose_mul {x j k : ℕ} (hjk : j ≤ k) :
    (x.descFactorial k : ℝ) / ((k - j).factorial * (j.factorial : ℝ)) =
      (x.choose k : ℝ) * (k.choose j : ℝ) := by
  have hfacNat : k.choose j * j.factorial * (k - j).factorial = k.factorial :=
    Nat.choose_mul_factorial_mul_factorial hjk
  have hfacReal : (k.choose j : ℝ) * (j.factorial : ℝ) * ((k - j).factorial : ℝ) =
      (k.factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  norm_num
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hkjfac : ((k - j).factorial : ℝ) ≠ 0 := by positivity
  have hkchoose : (k.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hjk))
  field_simp [hjfac, hkjfac, hkchoose]
  rw [← hfacReal]
  ring

lemma descFactorial_add_div_factorials_eq_choose_mul (x j i : ℕ) :
    (x.descFactorial (j + i) : ℝ) / (i.factorial * (j.factorial : ℝ)) =
      (x.choose j : ℝ) * ((x - j).choose i : ℝ) := by
  have hdesc := descFactorial_div_factorials_eq_choose_mul
    (x := x) (j := j) (k := j + i) (Nat.le_add_right j i)
  have hchoose := Nat.choose_mul
    (n := x) (k := j + i) (s := j) (Nat.le_add_right j i)
  have hchooseReal :
      (x.choose (j + i) : ℝ) * ((j + i).choose j : ℝ) =
        (x.choose j : ℝ) * ((x - j).choose i : ℝ) := by
    simpa [Nat.add_sub_cancel_left] using (show
      ((x.choose (j + i) * (j + i).choose j : ℕ) : ℝ) =
        (x.choose j * (x - j).choose ((j + i) - j) : ℕ) by
          exact_mod_cast hchoose)
  simpa [Nat.add_sub_cancel_left] using hdesc.trans hchooseReal

lemma factorial_kernel_sum_eq_indicator {M x j : ℕ} (hxM : x ≤ M) :
    (∑ i ∈ Finset.range (M - j + 1),
        ((-1 : ℝ) ^ i) *
          ((x.descFactorial (j + i) : ℝ) / (i.factorial * (j.factorial : ℝ)))) =
      if x = j then 1 else 0 := by
  by_cases hjx : j ≤ x
  · have hsub : x - j ≤ M - j := Nat.sub_le_sub_right hxM j
    calc
      (∑ i ∈ Finset.range (M - j + 1),
          ((-1 : ℝ) ^ i) *
            ((x.descFactorial (j + i) : ℝ) / (i.factorial * (j.factorial : ℝ))))
          = ∑ i ∈ Finset.range (M - j + 1),
              (x.choose j : ℝ) * (((-1 : ℝ) ^ i) * ((x - j).choose i : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [descFactorial_add_div_factorials_eq_choose_mul]
            ring
      _ = (x.choose j : ℝ) *
            (∑ i ∈ Finset.range (M - j + 1),
              ((-1 : ℝ) ^ i) * ((x - j).choose i : ℝ)) := by
            rw [Finset.mul_sum]
      _ = (x.choose j : ℝ) * (if x - j = 0 then 1 else 0) := by
            rw [alternating_choose_sum_range_of_le hsub]
      _ = if x = j then 1 else 0 := by
            by_cases hxj : x = j
            · subst x
              simp
            · have hxsub : x - j ≠ 0 := by omega
              simp [hxj, hxsub]
  · have hxlt : x < j := Nat.lt_of_not_ge hjx
    have hzero : ∀ i : ℕ, x.descFactorial (j + i) = 0 := by
      intro i
      exact (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_of_lt_of_le hxlt (Nat.le_add_right j i))
    have hxj : x ≠ j := by omega
    simp [hzero, hxj]

lemma zpow_neg_nat_add_eq_inv_mul (r j i : ℕ) (hr : 0 < r) :
    ((r : ℝ) ^ (-(j + i : ℤ))) =
      (((r : ℝ) ^ j * (r : ℝ) ^ i)⁻¹) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  rw [zpow_neg]
  rw [zpow_add₀ hrR]
  rw [zpow_natCast, zpow_natCast]

lemma factorial_moment_term_eq_expPartial_term (r j i : ℕ) (hr : 0 < r) :
    (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
        ((r : ℝ) ^ (-(j + i : ℤ))) =
      (((r : ℝ) ^ j * (j.factorial : ℝ))⁻¹) *
        (((-(r : ℝ)⁻¹) ^ i) / (i.factorial : ℝ)) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hifac : (i.factorial : ℝ) ≠ 0 := by positivity
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [zpow_neg_nat_add_eq_inv_mul r j i hr]
  have hneg : (-(r : ℝ)⁻¹) = (-1 : ℝ) * (r : ℝ)⁻¹ := by ring
  rw [hneg, mul_pow, inv_pow]
  field_simp [hrR, hifac, hjfac, pow_ne_zero i hrR, pow_ne_zero j hrR]

end Complete
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

/-!
# Bivariate Poisson limit for two cycle counts

This file proves the joint local limit and weak convergence of the pair of
cycle counts of two distinct positive lengths in a uniform random permutation.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace Bivariate

lemma rCycleCount_one_eq_card_sub_cycleType_sum (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n 1 σ = n - σ.cycleType.sum := by
  rw [rCycleCount_one]
  rw [← JointCycleMomentsNS.fixedPointCountIn_fin n σ]
  rw [JointCycleMomentsNS.fixedPointCountIn]
  rw [Equiv.Perm.card_fixedPoints]
  simp [Fintype.card_fin]

lemma oneDimTerm_hasSum {r : ℕ} (hr : 0 < r) (i : ℕ) :
    HasSum (fun a : ℕ => oneDimTerm r i a)
      (ProbabilityTheory.poissonPMFReal (poissonRate r) i) := by
  have hexp :
      HasSum (fun a : ℕ => ((-(r : ℝ)⁻¹) ^ a) / (a.factorial : ℝ))
        (Real.exp (-(r : ℝ)⁻¹)) := by
    simpa [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-(r : ℝ)⁻¹))
  have hmain := hexp.mul_left (((r : ℝ) ^ i * (i.factorial : ℝ))⁻¹)
  convert hmain using 1
  · ext a
    rw [oneDimTerm]
    exact Complete.factorial_moment_term_eq_expPartial_term r i a hr
  · rw [ProbabilityTheory.poissonPMFReal]
    simp [poissonRate]
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    have hifac : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hrR, pow_ne_zero i hrR, hifac]

end Bivariate
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

/-!
# General joint factorial moments for permutation cycle counts

This file extends the fixed-length and two-length factorial-moment identities
to arbitrary finite families of distinct positive lengths.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace JointCycleMomentsGeneralNS

section GeneralFiniteNontrivial

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma cycleType_count_prod_containing_from_complement_ne {r : ℕ} (T : Finset ℕ)
    (k : ℕ → ℕ) (hrT : r ∉ T)
    (c : FM.CyclesOfLengthIn (α := α) r)
    (τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support}) :
    (∏ s ∈ T,
        (((FM.permComplementEquivContainingCycleIn c τ).1.cycleType.count s).descFactorial
          (k s))) =
      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
  classical
  refine Finset.prod_congr rfl ?_
  intro s hs
  have hsr : s ≠ r := by
    intro hsr
    exact hrT (by simpa [hsr] using hs)
  rw [JointCycleMomentsNS.cycleType_count_containing_from_complement_ne
    (α := α) (s := s) (r := r) hsr c τ]

theorem cycleType_count_factorialMoment_sum_insert_in {r : ℕ} {T : Finset ℕ}
    (k : ℕ → ℕ) (hrT : r ∉ T) (hr : 2 ≤ r)
    (ihT :
      ∀ {β : Type u} [Fintype β] [DecidableEq β],
        (∑ s ∈ T, s * k s ≤ Fintype.card β) →
          (∏ s ∈ T, s ^ k s) *
              (∑ σ : Equiv.Perm β,
                ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
            (Fintype.card β).factorial)
    {a : ℕ} (h : r * a + ∑ s ∈ T, s * k s ≤ Fintype.card α) :
    r ^ a * (∏ s ∈ T, s ^ k s) *
        (∑ σ : Equiv.Perm α,
          (σ.cycleType.count r).descFactorial a *
            ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction a with
  | zero =>
      intro α _ _ h
      have hT : ∑ s ∈ T, s * k s ≤ Fintype.card α := by simpa using h
      simpa [mul_assoc] using ihT (β := α) hT
  | succ a iha =>
      intro α _ _ h
      have hrα : r ≤ Fintype.card α := by
        calc
          r = r * 1 := by simp
          _ ≤ r * (a + 1) := Nat.mul_le_mul_left r (Nat.succ_pos a)
          _ ≤ Fintype.card α := by omega
      have hrec_card :
          r * a + ∑ s ∈ T, s * k s ≤ Fintype.card α - r := by
        apply Nat.le_sub_of_add_le
        calc
          r * a + ∑ s ∈ T, s * k s + r =
              r * (a + 1) + ∑ s ∈ T, s * k s := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α,
            (σ.cycleType.count r).descFactorial (a + 1) *
              ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
            ∑ c : FM.CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial a *
                  ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
        calc
          (∑ σ : Equiv.Perm α,
            (σ.cycleType.count r).descFactorial (a + 1) *
              ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s))
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (FM.CyclesOfLengthOfPermIn (α := α) r σ) *
                    (((σ.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [FM.card_cyclesOfLengthOfPermIn (α := α) (r := r) σ]
                rw [FM.descFactorial_succ_eq_mul_pred]
                ring
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _c : FM.CyclesOfLengthOfPermIn (α := α) r σ,
                    (((σ.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ x : FM.CycleByPermIn (α := α) r,
                  (((x.1.cycleType.count r - 1).descFactorial a) *
                    ∏ s ∈ T, (x.1.cycleType.count s).descFactorial (k s)) := by
                exact (Fintype.sum_sigma'
                  (fun σ (_c : FM.CyclesOfLengthOfPermIn (α := α) r σ) =>
                    (((σ.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)))).symm
          _ = ∑ x : FM.CycleByCycleIn (α := α) r,
                  (((x.2.1.cycleType.count r - 1).descFactorial a) *
                    ∏ s ∈ T, (x.2.1.cycleType.count s).descFactorial (k s)) := by
                exact Fintype.sum_equiv (FM.cycleByPermEquivCycleByCycleIn (α := α) r)
                  (fun x : FM.CycleByPermIn (α := α) r =>
                    (((x.1.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (x.1.cycleType.count s).descFactorial (k s)))
                  (fun x : FM.CycleByCycleIn (α := α) r =>
                    (((x.2.1.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (x.2.1.cycleType.count s).descFactorial (k s)))
                  (by intro x; rfl)
          _ = ∑ c : FM.CyclesOfLengthIn (α := α) r,
                  ∑ σ : FM.PermContainingCycleIn c,
                    (((σ.1.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.1.cycleType.count s).descFactorial (k s)) := by
                rw [Fintype.sum_sigma]
          _ = ∑ c : FM.CyclesOfLengthIn (α := α) r,
                  ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
                refine Finset.sum_congr rfl ?_
                intro c _hc
                exact (Fintype.sum_equiv (FM.permComplementEquivContainingCycleIn c)
                  (fun τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} =>
                    (τ.cycleType.count r).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))
                  (fun σ : FM.PermContainingCycleIn c =>
                    (((σ.1.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.1.cycleType.count s).descFactorial (k s)))
                  (by
                    intro τ
                    change
                      (τ.cycleType.count r).descFactorial a *
                          (∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
                        ((((FM.permComplementEquivContainingCycleIn c) τ).1.cycleType.count r -
                            1).descFactorial a *
                          ∏ s ∈ T,
                            ((((FM.permComplementEquivContainingCycleIn c) τ).1.cycleType.count s).descFactorial
                              (k s)))
                    rw [← FM.cycleType_count_containing_from_complement (k := a) c τ]
                    rw [← cycleType_count_prod_containing_from_complement_ne
                      (α := α) (r := r) T k hrT c τ])).symm
      have hinner :
          ∀ c : FM.CyclesOfLengthIn (α := α) r,
            r ^ a * (∏ s ∈ T, s ^ k s) *
                (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                  (τ.cycleType.count r).descFactorial a *
                    ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card α - r).factorial := by
        intro c
        have hc_card :
            Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support} =
              Fintype.card α - r :=
          FM.card_complement_cycle_support_in c
        have hrec :
            r ^ a * (∏ s ∈ T, s ^ k s) *
                (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                  (τ.cycleType.count r).descFactorial a *
                    ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support}).factorial :=
          iha (α := {x : α // x ∉ (c : Equiv.Perm α).support}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        r ^ (a + 1) * (∏ s ∈ T, s ^ k s) *
            (∑ c : FM.CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial a *
                  ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))
            = r * (∑ c : FM.CyclesOfLengthIn (α := α) r,
                r ^ a * (∏ s ∈ T, s ^ k s) *
                  (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))) := by
              rw [pow_succ, ← Finset.mul_sum]
              ring
        _ = r * (∑ _c : FM.CyclesOfLengthIn (α := α) r,
              (Fintype.card α - r).factorial) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro c _hc
              exact hinner c
        _ = r * (Fintype.card (FM.CyclesOfLengthIn (α := α) r) *
              (Fintype.card α - r).factorial) := by
              rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = (Fintype.card α).factorial := by
              rw [FM.card_cyclesOfLengthIn (α := α) hr hrα]
              have hr0 : r ≠ 0 := by omega
              have hfac : r.factorial = (r - 1).factorial * r := by
                rw [Nat.mul_comm, Nat.mul_factorial_pred hr0]
              calc
                r * (((r - 1).factorial * (Fintype.card α).choose r) *
                    (Fintype.card α - r).factorial)
                    = (Fintype.card α).choose r * r.factorial *
                        (Fintype.card α - r).factorial := by
                      rw [hfac]
                      ring
                _ = (Fintype.card α).factorial := by
                      exact Nat.choose_mul_factorial_mul_factorial hrα

theorem cycleType_count_factorialMoment_sum_finset_in (S : Finset ℕ) :
    ∀ {α : Type u} [Fintype α] [DecidableEq α] (k : ℕ → ℕ),
      (∀ r ∈ S, 2 ≤ r) →
      (∑ r ∈ S, r * k r ≤ Fintype.card α) →
      (∏ r ∈ S, r ^ k r) *
          (∑ σ : Equiv.Perm α,
            ∏ r ∈ S, (σ.cycleType.count r).descFactorial (k r)) =
      (Fintype.card α).factorial := by
  classical
  intro α _ _ k hpos h
  induction S using Finset.induction generalizing α k with
  | empty =>
    simp [Fintype.card_perm]
  | insert r T hrT ih =>
    have hr : 2 ≤ r := hpos r (Finset.mem_insert_self r T)
    have hTpos : ∀ s ∈ T, 2 ≤ s := by
      intro s hs
      exact hpos s (Finset.mem_insert_of_mem hs)
    have ihT :
        ∀ {β : Type u} [Fintype β] [DecidableEq β],
          (∑ s ∈ T, s * k s ≤ Fintype.card β) →
            (∏ s ∈ T, s ^ k s) *
                (∑ σ : Equiv.Perm β,
                  ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card β).factorial := by
      intro β _ _ hb
      exact ih (α := β) (k := k) hTpos hb
    have h' : r * k r + ∑ s ∈ T, s * k s ≤ Fintype.card α := by
      simpa [Finset.sum_insert, hrT] using h
    have hmain :=
      cycleType_count_factorialMoment_sum_insert_in
        (α := α) (r := r) (T := T) (k := k) hrT hr ihT (a := k r) h'
    simpa [Finset.prod_insert, hrT, mul_assoc] using hmain

end GeneralFiniteNontrivial

section GeneralFiniteWithFixedPoints

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma cycleType_count_prod_fixingPoint_from_complement (T : Finset ℕ)
    (k : ℕ → ℕ) (x : α) (τ : Equiv.Perm {y : α // y ≠ x}) :
    (∏ s ∈ T, (((JointCycleMomentsNS.permComplementEquivFixingPointIn
        (α := α) x τ).1.cycleType.count s).descFactorial (k s))) =
      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
  classical
  refine Finset.prod_congr rfl ?_
  intro s _hs
  rw [JointCycleMomentsNS.cycleType_count_fixingPoint_from_complement
    (α := α) (s := s) x τ]

theorem fixedPoint_cycleType_count_factorialMoment_sum_finset_in (T : Finset ℕ)
    (k : ℕ → ℕ) (hpos : ∀ s ∈ T, 2 ≤ s) {a : ℕ}
    (h : a + ∑ s ∈ T, s * k s ≤ Fintype.card α) :
    (∏ s ∈ T, s ^ k s) *
        (∑ σ : Equiv.Perm α,
          (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial a *
            ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction a with
  | zero =>
      intro α _ _ h
      have hT : ∑ s ∈ T, s * k s ≤ Fintype.card α := by simpa using h
      simpa [mul_assoc] using
        cycleType_count_factorialMoment_sum_finset_in
          (S := T) (α := α) k hpos hT
  | succ a iha =>
      intro α _ _ h
      have hcard0 : Fintype.card α ≠ 0 := by omega
      have hrec_card :
          a + ∑ s ∈ T, s * k s ≤ Fintype.card α - 1 := by
        apply Nat.le_sub_of_add_le
        calc
          a + ∑ s ∈ T, s * k s + 1 =
              a + 1 + ∑ s ∈ T, s * k s := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α,
            (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial (a + 1) *
              ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
            ∑ x : α,
              ∑ τ : Equiv.Perm {y : α // y ≠ x},
                (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                  ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
        calc
          (∑ σ : Equiv.Perm α,
            (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial (a + 1) *
              ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s))
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (JointCycleMomentsNS.FixedPointsOfPermIn (α := α) σ) *
                    (((JointCycleMomentsNS.fixedPointCountIn σ - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [JointCycleMomentsNS.fixedPointCountIn]
                rw [FM.descFactorial_succ_eq_mul_pred]
                ring
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _x : JointCycleMomentsNS.FixedPointsOfPermIn (α := α) σ,
                    (((JointCycleMomentsNS.fixedPointCountIn σ - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ z : JointCycleMomentsNS.FixedPointByPermIn (α := α),
                  (((JointCycleMomentsNS.fixedPointCountIn z.1 - 1).descFactorial a) *
                    ∏ s ∈ T, (z.1.cycleType.count s).descFactorial (k s)) := by
                exact (Fintype.sum_sigma'
                  (fun σ (_x : JointCycleMomentsNS.FixedPointsOfPermIn (α := α) σ) =>
                    (((JointCycleMomentsNS.fixedPointCountIn σ - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)))).symm
          _ = ∑ z : JointCycleMomentsNS.FixedPointByPointIn (α := α),
                  (((JointCycleMomentsNS.fixedPointCountIn z.2.1 - 1).descFactorial a) *
                    ∏ s ∈ T, (z.2.1.cycleType.count s).descFactorial (k s)) := by
                exact Fintype.sum_equiv
                  (JointCycleMomentsNS.fixedPointByPermEquivByPointIn (α := α))
                  (fun z : JointCycleMomentsNS.FixedPointByPermIn (α := α) =>
                    (((JointCycleMomentsNS.fixedPointCountIn z.1 - 1).descFactorial a) *
                      ∏ s ∈ T, (z.1.cycleType.count s).descFactorial (k s)))
                  (fun z : JointCycleMomentsNS.FixedPointByPointIn (α := α) =>
                    (((JointCycleMomentsNS.fixedPointCountIn z.2.1 - 1).descFactorial a) *
                      ∏ s ∈ T, (z.2.1.cycleType.count s).descFactorial (k s)))
                  (by intro z; rfl)
          _ = ∑ x : α,
                  ∑ σ : JointCycleMomentsNS.PermFixingPointIn (α := α) x,
                    (((JointCycleMomentsNS.fixedPointCountIn σ.1 - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.1.cycleType.count s).descFactorial (k s)) := by
                rw [Fintype.sum_sigma]
          _ = ∑ x : α,
                  ∑ τ : Equiv.Perm {y : α // y ≠ x},
                    (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
                refine Finset.sum_congr rfl ?_
                intro x _hx
                exact (Fintype.sum_equiv
                  (JointCycleMomentsNS.permComplementEquivFixingPointIn (α := α) x)
                  (fun τ : Equiv.Perm {y : α // y ≠ x} =>
                    (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))
                  (fun σ : JointCycleMomentsNS.PermFixingPointIn (α := α) x =>
                    (((JointCycleMomentsNS.fixedPointCountIn σ.1 - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.1.cycleType.count s).descFactorial (k s)))
                  (by
                    intro τ
                    change
                      (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                          (∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
                        ((JointCycleMomentsNS.fixedPointCountIn
                            ((JointCycleMomentsNS.permComplementEquivFixingPointIn
                              (α := α) x) τ).1 - 1).descFactorial a *
                          ∏ s ∈ T,
                            ((((JointCycleMomentsNS.permComplementEquivFixingPointIn
                              (α := α) x) τ).1.cycleType.count s).descFactorial (k s)))
                    rw [← JointCycleMomentsNS.fixedPointCount_fixingPoint_from_complement_desc
                      (α := α) x τ]
                    rw [← cycleType_count_prod_fixingPoint_from_complement
                      (α := α) T k x τ])).symm
      have hinner :
          ∀ x : α,
            (∏ s ∈ T, s ^ k s) *
                (∑ τ : Equiv.Perm {y : α // y ≠ x},
                  (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                    ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card α - 1).factorial := by
        intro x
        have hc_card :
            Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 :=
          JointCycleMomentsNS.card_complement_point x
        have hrec :
            (∏ s ∈ T, s ^ k s) *
                (∑ τ : Equiv.Perm {y : α // y ≠ x},
                  (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                    ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card {y : α // y ≠ x}).factorial :=
          iha (α := {y : α // y ≠ x}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        (∏ s ∈ T, s ^ k s) *
            (∑ x : α,
              ∑ τ : Equiv.Perm {y : α // y ≠ x},
                (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                  ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))
            = ∑ x : α,
                (∏ s ∈ T, s ^ k s) *
                  (∑ τ : Equiv.Perm {y : α // y ≠ x},
                    (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) := by
              rw [Finset.mul_sum]
        _ = ∑ _x : α, (Fintype.card α - 1).factorial := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              exact hinner x
        _ = Fintype.card α * (Fintype.card α - 1).factorial := by
              rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = (Fintype.card α).factorial := by
              exact Nat.mul_factorial_pred hcard0

end GeneralFiniteWithFixedPoints

section FinCycleCounts

theorem rCycleCount_factorialMoment_sum_finset {n : ℕ} (S : Finset ℕ)
    (k : ℕ → ℕ) (hpos : ∀ r ∈ S, 0 < r)
    (h : ∑ r ∈ S, r * k r ≤ n) :
    (∏ r ∈ S, r ^ k r) *
        (∑ σ : Equiv.Perm (Fin n),
          ∏ r ∈ S, (rCycleCount n r σ).descFactorial (k r)) =
      n.factorial := by
  classical
  by_cases h1 : 1 ∈ S
  · have hSinsert : insert 1 (S.erase 1) = S := Finset.insert_erase h1
    have hTpos : ∀ r ∈ S.erase 1, 2 ≤ r := by
      intro r hr
      have hrne : r ≠ 1 := (Finset.mem_erase.mp hr).1
      have hrS : r ∈ S := (Finset.mem_erase.mp hr).2
      have hrpos : 0 < r := hpos r hrS
      omega
    have hbound : k 1 + ∑ r ∈ S.erase 1, r * k r ≤ n := by
      have h' : ∑ r ∈ insert 1 (S.erase 1), r * k r ≤ n := by
        simpa [hSinsert] using h
      simpa [Finset.sum_insert, one_mul] using h'
    have hfixed :
        (∏ r ∈ S.erase 1, r ^ k r) *
            (∑ σ : Equiv.Perm (Fin n),
              (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial (k 1) *
                ∏ r ∈ S.erase 1, (σ.cycleType.count r).descFactorial (k r)) =
          n.factorial := by
      simpa [Fintype.card_fin] using
        fixedPoint_cycleType_count_factorialMoment_sum_finset_in
          (α := Fin n) (T := S.erase 1) (k := k) hTpos (a := k 1)
          (by simpa [Fintype.card_fin] using hbound)
    have hpow :
        (∏ r ∈ insert 1 (S.erase 1), r ^ k r) =
          ∏ r ∈ S.erase 1, r ^ k r := by
      rw [Finset.prod_insert (by simp)]
      simp
    have hsum :
        (∑ σ : Equiv.Perm (Fin n),
          ∏ r ∈ insert 1 (S.erase 1), (rCycleCount n r σ).descFactorial (k r)) =
          ∑ σ : Equiv.Perm (Fin n),
            (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial (k 1) *
              ∏ r ∈ S.erase 1, (σ.cycleType.count r).descFactorial (k r) := by
      refine Finset.sum_congr rfl ?_
      intro σ _hσ
      rw [Finset.prod_insert (by simp)]
      rw [rCycleCount_one]
      rw [← JointCycleMomentsNS.fixedPointCountIn_fin n σ]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro r hr
      have hrne : r ≠ 1 := (Finset.mem_erase.mp hr).1
      rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    rw [← hSinsert, hpow, hsum]
    exact hfixed
  · have hnontriv : ∀ r ∈ S, 2 ≤ r := by
      intro r hr
      have hrpos : 0 < r := hpos r hr
      have hrne : r ≠ 1 := by
        intro hr1
        exact h1 (by simpa [hr1] using hr)
      omega
    have hsum :
        (∑ σ : Equiv.Perm (Fin n),
          ∏ r ∈ S, (rCycleCount n r σ).descFactorial (k r)) =
          ∑ σ : Equiv.Perm (Fin n),
            ∏ r ∈ S, (σ.cycleType.count r).descFactorial (k r) := by
      refine Finset.sum_congr rfl ?_
      intro σ _hσ
      refine Finset.prod_congr rfl ?_
      intro r hr
      have hrne : r ≠ 1 := by
        intro hr1
        exact h1 (by simpa [hr1] using hr)
      rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    rw [hsum]
    simpa [Fintype.card_fin] using
      cycleType_count_factorialMoment_sum_finset_in
        (S := S) (α := Fin n) k hnontriv (by simpa [Fintype.card_fin] using h)

theorem factorialMoment_rCycle_finset {n : ℕ} (S : Finset ℕ)
    (k : ℕ → ℕ) (hpos : ∀ r ∈ S, 0 < r)
    (h : ∑ r ∈ S, r * k r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) =
      ∏ r ∈ S, (r : ℝ) ^ (-(k r : ℤ)) := by
  classical
  unfold FixedPointsPoissonNS.uniformPermExpectation
  have hsumNat :=
    rCycleCount_factorialMoment_sum_finset (n := n) (S := S) (k := k) hpos h
  have hsumReal :
      (∏ r ∈ S, (r : ℝ) ^ k r) *
          (∑ σ : Equiv.Perm (Fin n),
            ∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) =
        (n.factorial : ℝ) := by
    exact_mod_cast hsumNat
  have hprod_pos : 0 < ∏ r ∈ S, (r : ℝ) ^ k r := by
    refine Finset.prod_pos ?_
    intro r hr
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hpos r hr
    exact pow_pos hrR (k r)
  have hprod_ne : (∏ r ∈ S, (r : ℝ) ^ k r) ≠ 0 := ne_of_gt hprod_pos
  have hnfac_ne : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    (∑ σ : Equiv.Perm (Fin n),
          ∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) /
        (n.factorial : ℝ)
        = ((n.factorial : ℝ) / (∏ r ∈ S, (r : ℝ) ^ k r)) /
            (n.factorial : ℝ) := by
          rw [← hsumReal]
          field_simp [hprod_ne]
    _ = (∏ r ∈ S, (r : ℝ) ^ k r)⁻¹ := by
          field_simp [hprod_ne, hnfac_ne]
    _ = ∏ r ∈ S, (r : ℝ) ^ (-(k r : ℤ)) := by
          rw [← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl ?_
          intro r _hr
          simp [zpow_neg, zpow_natCast]

end FinCycleCounts
end JointCycleMomentsGeneralNS
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

/-!
# Multivariate Poisson limits for finitely many cycle counts

This file contains the finite-product discrete bridge and the basic singleton
mass identities for vectors of cycle counts.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace Multivariate

lemma Multiset.sum_count_mul_le_sum (S : Finset ℕ) :
    ∀ m : Multiset ℕ, ∑ r ∈ S, m.count r * r ≤ m.sum := by
  classical
  intro m
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | cons a m ih =>
      by_cases ha : a ∈ S
      · have hsum_cons_erase :
            (∑ r ∈ S.erase a, (a ::ₘ m).count r * r) =
              ∑ r ∈ S.erase a, m.count r * r := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hra : r ≠ a := (Finset.mem_erase.mp hr).1
          rw [Multiset.count_cons_of_ne hra]
        have hsum_m :
            (∑ r ∈ S.erase a, m.count r * r) + m.count a * a =
              ∑ r ∈ S, m.count r * r := by
          exact Finset.sum_erase_add S (fun r => m.count r * r) ha
        calc
          (∑ r ∈ S, (a ::ₘ m).count r * r)
              = (∑ r ∈ S.erase a, (a ::ₘ m).count r * r) +
                  (a ::ₘ m).count a * a := by
                    exact (Finset.sum_erase_add S
                      (fun r => (a ::ₘ m).count r * r) ha).symm
          _ = (∑ r ∈ S.erase a, m.count r * r) + (m.count a + 1) * a := by
                    rw [hsum_cons_erase, Multiset.count_cons_self]
          _ = (∑ r ∈ S.erase a, m.count r * r) + (m.count a * a + a) := by
                    rw [Nat.add_mul]
                    simp
          _ = ((∑ r ∈ S.erase a, m.count r * r) + m.count a * a) + a := by
                    rw [Nat.add_assoc]
          _ = (∑ r ∈ S, m.count r * r) + a := by
                    rw [hsum_m]
          _ ≤ m.sum + a := Nat.add_le_add_right ih a
          _ = (a ::ₘ m).sum := by
                    simp [Nat.add_comm]
      · have hsum_cons :
            (∑ r ∈ S, (a ::ₘ m).count r * r) =
              ∑ r ∈ S, m.count r * r := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hra : r ≠ a := by
            intro h
            exact ha (by simpa [h] using hr)
          rw [Multiset.count_cons_of_ne hra]
        calc
          (∑ r ∈ S, (a ::ₘ m).count r * r)
              = ∑ r ∈ S, m.count r * r := hsum_cons
          _ ≤ m.sum := ih
          _ ≤ (a ::ₘ m).sum := by
                simp

lemma rCycleCount_finset_weight_le_card {n : ℕ} (S : Finset ℕ)
    (σ : Equiv.Perm (Fin n)) :
    ∑ r ∈ S, r * rCycleCount n r σ ≤ n := by
  classical
  have hcycle_le : σ.cycleType.sum ≤ n := by
    simpa [Fintype.card_fin] using Equiv.Perm.sum_cycleType_le σ
  by_cases h1 : 1 ∈ S
  · let T : Finset ℕ := S.erase 1
    have hcountT :
        ∑ r ∈ T, r * rCycleCount n r σ ≤ σ.cycleType.sum := by
      calc
        (∑ r ∈ T, r * rCycleCount n r σ)
            = ∑ r ∈ T, σ.cycleType.count r * r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrne : r ≠ 1 := (Finset.mem_erase.mp hr).1
                rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
                rw [Nat.mul_comm]
        _ ≤ σ.cycleType.sum := Multiset.sum_count_mul_le_sum T σ.cycleType
    have hfixed := Bivariate.rCycleCount_one_eq_card_sub_cycleType_sum n σ
    calc
      (∑ r ∈ S, r * rCycleCount n r σ)
          = (∑ r ∈ T, r * rCycleCount n r σ) + rCycleCount n 1 σ := by
              dsimp [T]
              rw [← Finset.sum_erase_add S (fun r => r * rCycleCount n r σ) h1]
              simp
      _ = (∑ r ∈ T, r * rCycleCount n r σ) + (n - σ.cycleType.sum) := by
              rw [hfixed]
      _ ≤ σ.cycleType.sum + (n - σ.cycleType.sum) := by
              exact Nat.add_le_add_right hcountT _
      _ = n := Nat.add_sub_of_le hcycle_le
  · calc
      (∑ r ∈ S, r * rCycleCount n r σ)
          = ∑ r ∈ S, σ.cycleType.count r * r := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              have hrne : r ≠ 1 := by
                intro h
                exact h1 (by simpa [h] using hr)
              rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
              rw [Nat.mul_comm]
      _ ≤ σ.cycleType.sum := Multiset.sum_count_mul_le_sum S σ.cycleType
      _ ≤ n := hcycle_le

lemma multivariate_rCycleCount_weight_le_card {m n : ℕ} (lengths : Fin m → ℕ)
    (hinj : Function.Injective lengths) (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin m, lengths i * rCycleCount n (lengths i) σ ≤ n := by
  classical
  let S : Finset ℕ := Finset.image lengths Finset.univ
  have hinjOn : Set.InjOn lengths (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro i _hi j _hj hij
    exact hinj hij
  have hsumS :
      (∑ r ∈ S, r * rCycleCount n r σ) =
        ∑ i : Fin m, lengths i * rCycleCount n (lengths i) σ := by
    dsimp [S]
    rw [Finset.sum_image hinjOn]
  simpa [hsumS] using rCycleCount_finset_weight_le_card (n := n) S σ

lemma multivariate_factorial_moment_eval {m n : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths)
    (a : Fin m → ℕ) (hweight : ∑ i : Fin m, lengths i * a i ≤ n) :
    (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) /
      (n.factorial : ℝ) =
      ∏ i : Fin m, (lengths i : ℝ) ^ (-(a i : ℤ)) := by
  classical
  let S : Finset ℕ := Finset.image lengths Finset.univ
  let k : ℕ → ℕ := fun r =>
    if h : ∃ i : Fin m, lengths i = r then a (Classical.choose h) else 0
  have hk : ∀ i : Fin m, k (lengths i) = a i := by
    intro i
    have h : ∃ j : Fin m, lengths j = lengths i := ⟨i, rfl⟩
    have hchoose : lengths (Classical.choose h) = lengths i := Classical.choose_spec h
    have hidx : Classical.choose h = i := hinj hchoose
    simp [k, h, hidx]
  have hinjOn : Set.InjOn lengths (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro i _hi j _hj hij
    exact hinj hij
  have hposS : ∀ r ∈ S, 0 < r := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨i, _hi, rfl⟩
    exact hpos i
  have hsumS : (∑ r ∈ S, r * k r) = ∑ i : Fin m, lengths i * a i := by
    dsimp [S]
    rw [Finset.sum_image hinjOn]
    simp [hk]
  have hweightS : ∑ r ∈ S, r * k r ≤ n := by
    simpa [hsumS] using hweight
  have hprod_desc :
      ∀ σ : Equiv.Perm (Fin n),
        (∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) =
          ∏ i : Fin m,
            ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ) := by
    intro σ
    dsimp [S]
    rw [Finset.prod_image hinjOn]
    simp [hk]
  have hprod_pow :
      (∏ r ∈ S, (r : ℝ) ^ (-(k r : ℤ))) =
        ∏ i : Fin m, (lengths i : ℝ) ^ (-(a i : ℤ)) := by
    dsimp [S]
    rw [Finset.prod_image hinjOn]
    simp [hk]
  have hfm :=
    JointCycleMomentsGeneralNS.factorialMoment_rCycle_finset
      (n := n) (S := S) (k := k) hposS hweightS
  unfold FixedPointsPoissonNS.uniformPermExpectation at hfm
  calc
    (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) /
      (n.factorial : ℝ)
        =
      (∑ σ : Equiv.Perm (Fin n),
        ∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) /
      (n.factorial : ℝ) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro σ _hσ
        exact (hprod_desc σ).symm
    _ = ∏ r ∈ S, (r : ℝ) ^ (-(k r : ℤ)) := hfm
    _ = ∏ i : Fin m, (lengths i : ℝ) ^ (-(a i : ℤ)) := hprod_pow

lemma multivariate_factorial_moment_zero_of_lt {m n : ℕ} (lengths : Fin m → ℕ)
    (hinj : Function.Injective lengths) (a : Fin m → ℕ)
    (h : n < ∑ i : Fin m, lengths i * a i) :
    (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) /
      (n.factorial : ℝ) = 0 := by
  classical
  suffices
      (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) = 0 by
    rw [this]
    simp
  refine Finset.sum_eq_zero ?_
  intro σ _hσ
  by_cases hall : ∀ i : Fin m, a i ≤ rCycleCount n (lengths i) σ
  · have huse :
        (∑ i : Fin m, lengths i * a i) ≤
          ∑ i : Fin m, lengths i * rCycleCount n (lengths i) σ := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact Nat.mul_le_mul_left (lengths i) (hall i)
    have hcard := multivariate_rCycleCount_weight_le_card (n := n) lengths hinj σ
    omega
  · have hex : ∃ i : Fin m, ¬ a i ≤ rCycleCount n (lengths i) σ := by
      simpa [not_forall] using hall
    rcases hex with ⟨i, hi⟩
    have hzeroNat :
        (rCycleCount n (lengths i) σ).descFactorial (a i) = 0 :=
      (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_of_not_ge hi)
    have hzeroReal :
        ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ) = 0 := by
      exact_mod_cast hzeroNat
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzeroReal

lemma multivariate_factorial_moment_eval_if {m n : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths)
    (a : Fin m → ℕ) :
    (∑ σ : Equiv.Perm (Fin n),
        ∏ i : Fin m, ((rCycleCount n (lengths i) σ).descFactorial (a i) : ℝ)) /
      (n.factorial : ℝ) =
      if ∑ i : Fin m, lengths i * a i ≤ n then
        ∏ i : Fin m, (lengths i : ℝ) ^ (-(a i : ℤ))
      else 0 := by
  by_cases hle : ∑ i : Fin m, lengths i * a i ≤ n
  · simp [hle, multivariate_factorial_moment_eval
      (n := n) lengths hpos hinj a hle]
  · have hlt : n < ∑ i : Fin m, lengths i * a i := Nat.lt_of_not_ge hle
    simp [hle, multivariate_factorial_moment_zero_of_lt
      (n := n) lengths hinj a hlt]

lemma card_subtype_eq_sum_pi_indicator {ι α : Type*} [Fintype ι] [Fintype α]
    (X : ι → α → ℕ) (j : ι → ℕ) :
    (Fintype.card {a : α // ∀ i : ι, X i a = j i} : ℝ) =
      ∑ a : α, if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0 := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.sum_boole]

lemma pi_indicator_eq_kernel_sum {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → α → ℕ) {M j : ι → ℕ} (hX : ∀ a : α, ∀ i : ι, X i a ≤ M i)
    (a : α) :
    (if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0) =
      ∑ u ∈ Fintype.piFinset (fun i : ι => Finset.range (M i - j i + 1)),
        ∏ i : ι,
          ((-1 : ℝ) ^ (u i)) *
            (((X i a).descFactorial (j i + u i) : ℝ) /
              ((u i).factorial * ((j i).factorial : ℝ))) := by
  classical
  let U : ι → Finset ℕ := fun i => Finset.range (M i - j i + 1)
  let K : ι → ℕ → ℝ := fun i u =>
    ((-1 : ℝ) ^ u) *
      (((X i a).descFactorial (j i + u) : ℝ) /
        (u.factorial * ((j i).factorial : ℝ)))
  have hcoord :
      ∀ i : ι, (∑ u ∈ U i, K i u) = if X i a = j i then (1 : ℝ) else 0 := by
    intro i
    simpa [U, K] using
      Complete.factorial_kernel_sum_eq_indicator
        (M := M i) (x := X i a) (j := j i) (hX a i)
  calc
    (if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0)
        = ∏ i : ι, (if X i a = j i then (1 : ℝ) else 0) := by
          by_cases h : ∀ i : ι, X i a = j i
          · simp [h]
          · have hex : ∃ i : ι, X i a ≠ j i := by
              simpa [not_forall] using h
            rcases hex with ⟨i, hi⟩
            simp [h]
            exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
    _ = ∏ i : ι, ∑ u ∈ U i, K i u := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          exact (hcoord i).symm
    _ = ∑ u ∈ Fintype.piFinset U, ∏ i : ι, K i (u i) := by
          exact Finset.prod_univ_sum U K
    _ = ∑ u ∈ Fintype.piFinset (fun i : ι => Finset.range (M i - j i + 1)),
        ∏ i : ι,
          ((-1 : ℝ) ^ (u i)) *
            (((X i a).descFactorial (j i + u i) : ℝ) /
              ((u i).factorial * ((j i).factorial : ℝ))) := by
          rfl

/-- Finite multivariate pmf inversion in terms of mixed factorial moments. -/
lemma finite_pi_pmf_eq_factorial_moment_sum {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (X : ι → α → ℕ) {M j : ι → ℕ}
    (hX : ∀ a : α, ∀ i : ι, X i a ≤ M i) :
    (Fintype.card {a : α // ∀ i : ι, X i a = j i} : ℝ) /
        (Fintype.card α : ℝ) =
      ∑ u ∈ Fintype.piFinset (fun i : ι => Finset.range (M i - j i + 1)),
        (∏ i : ι, ((-1 : ℝ) ^ (u i)) /
          ((u i).factorial * ((j i).factorial : ℝ))) *
          ((∑ a : α,
            ∏ i : ι, ((X i a).descFactorial (j i + u i) : ℝ)) /
            (Fintype.card α : ℝ)) := by
  classical
  let U : ι → Finset ℕ := fun i => Finset.range (M i - j i + 1)
  let K : α → (ι → ℕ) → ℝ := fun a u =>
    ∏ i : ι,
      ((-1 : ℝ) ^ (u i)) *
        (((X i a).descFactorial (j i + u i) : ℝ) /
          ((u i).factorial * ((j i).factorial : ℝ)))
  let C : (ι → ℕ) → ℝ := fun u =>
    ∏ i : ι, ((-1 : ℝ) ^ (u i)) /
      ((u i).factorial * ((j i).factorial : ℝ))
  let D : α → (ι → ℕ) → ℝ := fun a u =>
    ∏ i : ι, ((X i a).descFactorial (j i + u i) : ℝ)
  have hpoint :
      ∀ a : α,
        (if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0) =
          ∑ u ∈ Fintype.piFinset U, K a u := by
    intro a
    simpa [U, K] using pi_indicator_eq_kernel_sum (X := X) (M := M) (j := j) hX a
  have hK : ∀ a : α, ∀ u : ι → ℕ, K a u = C u * D a u := by
    intro a u
    simp [K, C, D, Finset.prod_mul_distrib]
    ring
  calc
    (Fintype.card {a : α // ∀ i : ι, X i a = j i} : ℝ) /
        (Fintype.card α : ℝ)
        =
      (∑ a : α, if (∀ i : ι, X i a = j i) then (1 : ℝ) else 0) /
        (Fintype.card α : ℝ) := by
          rw [card_subtype_eq_sum_pi_indicator X j]
    _ = (∑ a : α, ∑ u ∈ Fintype.piFinset U, K a u) /
        (Fintype.card α : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact hpoint a
    _ = (∑ u ∈ Fintype.piFinset U, ∑ a : α, K a u) /
        (Fintype.card α : ℝ) := by
          congr 1
          exact Finset.sum_comm
    _ = ∑ u ∈ Fintype.piFinset U,
        (∑ a : α, K a u) / (Fintype.card α : ℝ) := by
          rw [Finset.sum_div]
    _ = ∑ u ∈ Fintype.piFinset U,
        C u * ((∑ a : α, D a u) / (Fintype.card α : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro u _hu
          calc
            (∑ a : α, K a u) / (Fintype.card α : ℝ)
                = (C u * ∑ a : α, D a u) / (Fintype.card α : ℝ) := by
                    congr 1
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro a _ha
                    exact hK a u
            _ = C u * ((∑ a : α, D a u) / (Fintype.card α : ℝ)) := by
                    ring
    _ = ∑ u ∈ Fintype.piFinset (fun i : ι => Finset.range (M i - j i + 1)),
        (∏ i : ι, ((-1 : ℝ) ^ (u i)) /
          ((u i).factorial * ((j i).factorial : ℝ))) *
          ((∑ a : α,
            ∏ i : ι, ((X i a).descFactorial (j i + u i) : ℝ)) /
            (Fintype.card α : ℝ)) := by
          rfl

lemma multivariate_formula_term_eq {m : ℕ} (lengths : Fin m → ℕ)
    (v u : Fin m → ℕ) :
    ((∏ i : Fin m, ((-1 : ℝ) ^ (u i))) /
      (∏ i : Fin m, ((u i).factorial * ((v i).factorial : ℝ)))) *
      (∏ i : Fin m, (lengths i : ℝ) ^ (-(u i : ℤ) + -(v i : ℤ))) =
      ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i) := by
  rw [← Finset.prod_div_distrib]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  simp [oneDimTerm, Bivariate.oneDimTerm]

theorem multivariatePMF_eq_formula {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths) :
    ∀ n : ℕ, ∀ v : Fin m → ℕ,
      multivariatePMF n lengths v = multivariatePMFFormula n lengths v := by
  classical
  intro n v
  have hinv := finite_pi_pmf_eq_factorial_moment_sum
    (ι := Fin m) (α := Equiv.Perm (Fin n))
    (X := fun i σ => rCycleCount n (lengths i) σ)
    (M := fun i => n / lengths i) (j := v)
    (fun σ i => Complete.rCycleCount_le_div (n := n) (r := lengths i) (hpos i) σ)
  have hpmf :
      multivariatePMF n lengths v =
        ∑ u ∈ Fintype.piFinset
          (fun i : Fin m => Finset.range (n / lengths i - v i + 1)),
          ((∏ i : Fin m, ((-1 : ℝ) ^ (u i))) /
            (∏ i : Fin m, ((u i).factorial * ((v i).factorial : ℝ)))) *
            ((∑ σ : Equiv.Perm (Fin n),
              ∏ i : Fin m,
                ((rCycleCount n (lengths i) σ).descFactorial (v i + u i) : ℝ)) /
              (n.factorial : ℝ)) := by
    unfold multivariatePMF
    simpa [Fintype.card_perm, Fintype.card_fin] using hinv
  rw [hpmf]
  unfold multivariatePMFFormula multivariateIndexFinset
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro u hu
  by_cases hle : ∑ i : Fin m, lengths i * (v i + u i) ≤ n
  · rw [multivariate_factorial_moment_eval_if
      (n := n) lengths hpos hinj (fun i : Fin m => v i + u i)]
    simp [hle]
    exact multivariate_formula_term_eq lengths v u
  · rw [multivariate_factorial_moment_eval_if
      (n := n) lengths hpos hinj (fun i : Fin m => v i + u i)]
    simp [hle]

lemma mem_multivariateIndexFinset_of_weight_le {m n : ℕ} {lengths v u : Fin m → ℕ}
    (hpos : ∀ i : Fin m, 0 < lengths i)
    (hweight : ∑ i : Fin m, lengths i * (v i + u i) ≤ n) :
    u ∈ multivariateIndexFinset n lengths v := by
  classical
  unfold multivariateIndexFinset
  refine Finset.mem_filter.2 ⟨?_, hweight⟩
  rw [Fintype.mem_piFinset]
  intro i
  have hpart : lengths i * (v i + u i) ≤ n := by
    exact (Finset.single_le_sum (fun j _hj => Nat.zero_le _)
      (Finset.mem_univ i)).trans hweight
  have hle : v i + u i ≤ n / lengths i :=
    (Nat.le_div_iff_mul_le (hpos i)).2 (by simpa [Nat.mul_comm] using hpart)
  exact Finset.mem_range.2
    (Nat.lt_succ_of_le (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hle)))

lemma multivariateIndexFinset_tendsto_atTop {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (v : Fin m → ℕ) :
    Tendsto (fun n : ℕ => multivariateIndexFinset n lengths v) atTop atTop := by
  classical
  refine Filter.tendsto_atTop_finset_of_monotone ?_ ?_
  · intro n n' hnn' u hu
    exact mem_multivariateIndexFinset_of_weight_le (n := n') (lengths := lengths)
      (v := v) hpos ((Finset.mem_filter.mp hu).2.trans hnn')
  · intro u
    exact ⟨∑ i : Fin m, lengths i * (v i + u i),
      mem_multivariateIndexFinset_of_weight_le (lengths := lengths) (v := v) hpos le_rfl⟩

lemma summable_norm_pi_oneDimTerm :
    ∀ {m : ℕ} (lengths : Fin m → ℕ), (∀ i : Fin m, 0 < lengths i) →
      (v : Fin m → ℕ) →
      Summable fun u : Fin m → ℕ =>
        ‖∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i)‖ := by
  intro m
  induction m with
  | zero =>
      intro lengths hpos v
      exact (hasSum_fintype
        (fun u : Fin 0 → ℕ =>
          ‖∏ i : Fin 0, oneDimTerm (lengths i) (v i) (u i)‖)).summable
  | succ m ih =>
      intro lengths hpos v
      let tailLengths : Fin m → ℕ := fun i => lengths i.succ
      let tailV : Fin m → ℕ := fun i => v i.succ
      have h0 :
          Summable fun a : ℕ => ‖oneDimTerm (lengths 0) (v 0) a‖ := by
        simpa [oneDimTerm] using
          (Bivariate.oneDimTerm_hasSum (r := lengths 0) (hpos 0) (v 0)).summable.abs
      have htail :
          Summable fun u : Fin m → ℕ =>
            ‖∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (u i)‖ :=
        ih tailLengths (fun i => hpos i.succ) tailV
      have hprod :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            ‖oneDimTerm (lengths 0) (v 0) p.1‖ *
              ‖∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i)‖ :=
        h0.mul_of_nonneg htail (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have hprod_norm :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            ‖oneDimTerm (lengths 0) (v 0) p.1 *
              (∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i))‖ := by
        simpa [norm_mul] using hprod
      let e : ℕ × (Fin m → ℕ) ≃ (Fin (m + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)
      have hcomp :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            ‖∏ i : Fin (m + 1), oneDimTerm (lengths i) (v i) ((e p) i)‖ := by
        convert hprod_norm using 1
        ext p
        rw [Fin.prod_univ_succ]
        simp [e, tailLengths, tailV, Fin.consEquiv_apply]
      exact (e.summable_iff).1 hcomp

-- The finite-product `HasSum` induction combines a dependent tail series with
-- `HasSum.mul`; the local heartbeat bump prevents a deterministic timeout in
-- the summability witness elaboration.
set_option maxHeartbeats 800000 in
lemma hasSum_pi_oneDimTerm :
    ∀ {m : ℕ} (lengths : Fin m → ℕ), (∀ i : Fin m, 0 < lengths i) →
      (v : Fin m → ℕ) →
      HasSum
        (fun u : Fin m → ℕ =>
          ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i))
        (poissonPiPMF lengths v) := by
  intro m
  induction m with
  | zero =>
      intro lengths hpos v
      simp [poissonPiPMF]
  | succ m ih =>
      intro lengths hpos v
      let tailLengths : Fin m → ℕ := fun i => lengths i.succ
      let tailV : Fin m → ℕ := fun i => v i.succ
      have h0 :
          HasSum (fun a : ℕ => oneDimTerm (lengths 0) (v 0) a)
            (ProbabilityTheory.poissonPMFReal (poissonRate (lengths 0)) (v 0)) := by
        simpa [oneDimTerm] using
          Bivariate.oneDimTerm_hasSum (r := lengths 0) (hpos 0) (v 0)
      have htail :
          HasSum
            (fun u : Fin m → ℕ =>
              ∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (u i))
            (poissonPiPMF tailLengths tailV) :=
        ih tailLengths (fun i => hpos i.succ) tailV
      have htail_abs :
          Summable fun u : Fin m → ℕ =>
            ‖∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (u i)‖ :=
        summable_norm_pi_oneDimTerm tailLengths (fun i => hpos i.succ) tailV
      have hprod_abs :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            ‖oneDimTerm (lengths 0) (v 0) p.1‖ *
              ‖∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i)‖ :=
        h0.summable.abs.mul_of_nonneg htail_abs
          (fun _ => abs_nonneg _) (fun _ => norm_nonneg _)
      have hprod_summable :
          Summable fun p : ℕ × (Fin m → ℕ) =>
            oneDimTerm (lengths 0) (v 0) p.1 *
              (∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i)) := by
        refine Summable.of_norm ?_
        simpa [norm_mul] using hprod_abs
      have hprod_hasSum :
          HasSum
            (fun p : ℕ × (Fin m → ℕ) =>
              oneDimTerm (lengths 0) (v 0) p.1 *
                (∏ i : Fin m, oneDimTerm (tailLengths i) (tailV i) (p.2 i)))
            (ProbabilityTheory.poissonPMFReal (poissonRate (lengths 0)) (v 0) *
              poissonPiPMF tailLengths tailV) :=
        h0.mul htail hprod_summable
      let e : ℕ × (Fin m → ℕ) ≃ (Fin (m + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)
      have hcomp :
          HasSum
            (fun p : ℕ × (Fin m → ℕ) =>
              ∏ i : Fin (m + 1), oneDimTerm (lengths i) (v i) ((e p) i))
            (poissonPiPMF lengths v) := by
        convert hprod_hasSum using 1
        · ext p
          rw [Fin.prod_univ_succ]
          simp [e, tailLengths, tailV, Fin.consEquiv_apply]
        · simp [poissonPiPMF, tailLengths, tailV, Fin.prod_univ_succ]
      exact (e.hasSum_iff).1 hcomp

theorem multivariatePMFFormula_tendsto_poissonPiPMF {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (v : Fin m → ℕ) :
    Tendsto (fun n : ℕ => multivariatePMFFormula n lengths v) atTop
      (𝓝 (poissonPiPMF lengths v)) := by
  have hsum := hasSum_pi_oneDimTerm lengths hpos v
  change Tendsto
    (fun n : ℕ => ∑ u ∈ multivariateIndexFinset n lengths v,
      ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i))
    atTop (𝓝 (poissonPiPMF lengths v))
  change Tendsto
    (fun t : Finset (Fin m → ℕ) => ∑ u ∈ t,
      ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i))
    atTop (𝓝 (poissonPiPMF lengths v)) at hsum
  exact hsum.comp (multivariateIndexFinset_tendsto_atTop lengths hpos v)

theorem multivariatePMF_tendsto_poissonPiPMF {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths)
    (v : Fin m → ℕ) :
    Tendsto (fun n : ℕ => multivariatePMF n lengths v) atTop
      (𝓝 (poissonPiPMF lengths v)) := by
  exact Tendsto.congr' (Eventually.of_forall fun n =>
    (multivariatePMF_eq_formula lengths hpos hinj n v).symm)
    (multivariatePMFFormula_tendsto_poissonPiPMF lengths hpos v)

/-- On `Fin m → ℕ`, pointwise singleton convergence implies weak convergence. -/
theorem probabilityMeasure_pi_nat_tendsto_of_tendsto_singleton {m : ℕ}
    {μs : ℕ → ProbabilityMeasure (Fin m → ℕ)} {μ : ProbabilityMeasure (Fin m → ℕ)}
    (h : ∀ v : Fin m → ℕ,
      Tendsto (fun n : ℕ => (μs n : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)))
        atTop
        (𝓝 ((μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ))))) :
    Tendsto μs atTop (𝓝 μ) := by
  classical
  refine MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat' ?_
  intro G _hG
  have hfinite_le :
      ∀ t : Finset (Fin m → ℕ), (∀ v ∈ t, v ∈ G) →
        (∑ v ∈ t, (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ))) ≤
          atTop.liminf (fun n : ℕ => (μs n : Measure (Fin m → ℕ)) G) := by
    intro t htG
    have hsum_tendsto :
        Tendsto
          (fun n : ℕ => ∑ v ∈ t,
            (μs n : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)))
          atTop
          (𝓝 (∑ v ∈ t, (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)))) :=
      tendsto_finset_sum t (fun v _hv => h v)
    rw [← hsum_tendsto.liminf_eq]
    refine Filter.liminf_le_liminf (Eventually.of_forall ?_)
      (by isBoundedDefault)
      (by isBoundedDefault)
    intro n
    have hdisj : (t : Set (Fin m → ℕ)).PairwiseDisjoint
        (fun v => ({v} : Set (Fin m → ℕ))) := by
      intro a _ha b _hb hne
      change Disjoint ({a} : Set (Fin m → ℕ)) ({b} : Set (Fin m → ℕ))
      rw [Set.disjoint_singleton_left]
      simpa using hne
    calc
      (∑ v ∈ t, (μs n : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)))
          = (μs n : Measure (Fin m → ℕ))
              (⋃ v ∈ t, ({v} : Set (Fin m → ℕ))) := by
              exact (MeasureTheory.measure_biUnion_finset hdisj
                (fun v _hv => measurableSet_singleton v)).symm
      _ ≤ (μs n : Measure (Fin m → ℕ)) G := by
              refine measure_mono ?_
              intro x hx
              simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
              rcases hx with ⟨v, hv, hxv⟩
              subst hxv
              exact htG x hv
  have hμG :
      (μ : Measure (Fin m → ℕ)) G =
        ∑' v : Fin m → ℕ, G.indicator
          (fun v => (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ))) v := by
    exact (Measure.tsum_indicator_apply_singleton (μ : Measure (Fin m → ℕ)) G
      G.to_countable.measurableSet).symm
  rw [hμG, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro t
  calc
    (∑ v ∈ t, G.indicator
        (fun v => (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ))) v)
        = ∑ v ∈ t.filter (fun v => v ∈ G),
            (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro v _hv
            by_cases hvG : v ∈ G
            · simp [hvG]
            · simp [hvG]
    _ ≤ atTop.liminf (fun n : ℕ => (μs n : Measure (Fin m → ℕ)) G) :=
            hfinite_le (t.filter (fun v => v ∈ G))
              (fun v hv => (Finset.mem_filter.mp hv).2)

/-- A real-valued pmf version of the finite-product discrete bridge. -/
theorem probabilityMeasure_pi_nat_tendsto_of_tendsto_pmfReal {m : ℕ}
    {p : ℕ → (Fin m → ℕ) → ℝ} {q : (Fin m → ℕ) → ℝ}
    {μs : ℕ → ProbabilityMeasure (Fin m → ℕ)} {μ : ProbabilityMeasure (Fin m → ℕ)}
    (hp : ∀ n v, (μs n : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) =
      ENNReal.ofReal (p n v))
    (hq : ∀ v, (μ : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) =
      ENNReal.ofReal (q v))
    (hconv : ∀ v : Fin m → ℕ, Tendsto (fun n : ℕ => p n v) atTop (𝓝 (q v))) :
    Tendsto μs atTop (𝓝 μ) :=
  probabilityMeasure_pi_nat_tendsto_of_tendsto_singleton fun v => by
    simpa [hp, hq] using ENNReal.tendsto_ofReal (hconv v)

lemma multivariate_law_singleton {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ)
    (v : Fin m → ℕ) :
    (multivariateLaw n lengths : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) =
      ENNReal.ofReal (multivariatePMF n lengths v) := by
  classical
  have hpre :
      (fun σ : Equiv.Perm (Fin n) => fun i : Fin m => rCycleCount n (lengths i) σ) ⁻¹'
          ({v} : Set (Fin m → ℕ)) =
        {σ : Equiv.Perm (Fin n) |
          ∀ i : Fin m, rCycleCount n (lengths i) σ = v i} := by
    ext σ
    simp [funext_iff]
  change
    (Measure.map
      (fun σ : Equiv.Perm (Fin n) => fun i : Fin m => rCycleCount n (lengths i) σ)
      (uniformPermMeasure n)) ({v} : Set (Fin m → ℕ)) =
        ENNReal.ofReal (multivariatePMF n lengths v)
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton v), hpre]
  unfold uniformPermMeasure
  rw [PMF.toMeasure_uniformOfFintype_apply]
  · rw [Fintype.card_perm, Fintype.card_fin]
    change
      (Fintype.card {σ : Equiv.Perm (Fin n) //
        ∀ i : Fin m, rCycleCount n (lengths i) σ = v i} : ℝ≥0∞) /
          (n.factorial : ℝ≥0∞) =
        ENNReal.ofReal (multivariatePMF n lengths v)
    have hcard :
        Fintype.card {σ : Equiv.Perm (Fin n) //
          ∀ i : Fin m, rCycleCount n (lengths i) σ = v i} =
          @Fintype.card {σ : Equiv.Perm (Fin n) //
            (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i) σ}
            (@Subtype.fintype (Equiv.Perm (Fin n))
              (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i)
              (fun _ => Fintype.decidableForallFintype) Equiv.instFintype) := by
      exact @Fintype.card_congr
        {σ : Equiv.Perm (Fin n) // ∀ i : Fin m, rCycleCount n (lengths i) σ = v i}
        {σ : Equiv.Perm (Fin n) //
          (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i) σ}
        (@Subtype.fintype (Equiv.Perm (Fin n))
          (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i)
          (fun a => Nat.decidableForallFin
            (fun i => rCycleCount n (lengths i) a = v i)) Equiv.instFintype)
        (@Subtype.fintype (Equiv.Perm (Fin n))
          (fun σ => ∀ i : Fin m, rCycleCount n (lengths i) σ = v i)
          (fun _ => Fintype.decidableForallFintype) Equiv.instFintype)
        (Equiv.refl _)
    unfold multivariatePMF
    rw [ENNReal.ofReal_div_of_pos]
    · congr
      · exact_mod_cast hcard
      · exact_mod_cast rfl
    · positivity
  · simp

lemma poissonPiMeasure_singleton {m : ℕ} (lengths : Fin m → ℕ) (v : Fin m → ℕ) :
    (poissonPiMeasure lengths : Measure (Fin m → ℕ)) ({v} : Set (Fin m → ℕ)) =
      ENNReal.ofReal (poissonPiPMF lengths v) := by
  rw [poissonPiMeasure, poissonPiPMF]
  change Measure.pi
      (fun i : Fin m => ProbabilityTheory.poissonMeasure (poissonRate (lengths i))) {v} =
    ENNReal.ofReal
      (∏ i : Fin m, ProbabilityTheory.poissonPMFReal (poissonRate (lengths i)) (v i))
  rw [Measure.pi_singleton]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · refine Finset.prod_congr rfl ?_
    intro i _hi
    exact poisson_law_singleton (poissonRate (lengths i)) (v i)
  · intro i _hi
    exact ProbabilityTheory.poissonPMFReal_nonneg

end Multivariate
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch9 AnalyticCombinatorics.Ch9.LimitLaws AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Multivariate
open Filter MeasureTheory
open scoped Topology ENNReal NNReal
theorem solution {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths) :
    Tendsto (fun n : ℕ => multivariateLaw n lengths) atTop
      (𝓝 (poissonPiMeasure lengths)) := by
  refine probabilityMeasure_pi_nat_tendsto_of_tendsto_pmfReal
    (p := fun n v => multivariatePMF n lengths v)
    (q := fun v => poissonPiPMF lengths v) ?_ ?_ ?_
  · intro n v
    exact multivariate_law_singleton n lengths v
  · intro v
    exact poissonPiMeasure_singleton lengths v
  · intro v
    exact multivariatePMF_tendsto_poissonPiPMF lengths hpos hinj v
