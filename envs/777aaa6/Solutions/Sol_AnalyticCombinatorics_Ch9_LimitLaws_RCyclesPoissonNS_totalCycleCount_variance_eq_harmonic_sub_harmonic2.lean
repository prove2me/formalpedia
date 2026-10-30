-- Prove2me | solution 1 for AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.totalCycleCount_variance_eq_harmonic_sub_harmonic2
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:58:50.194753+00:00
-- url     : https://prove2.me/submissions/65980d9c-9b2b-4cc0-9d60-a4fa31bd7890

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_FixedPointsPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_JointCycleMoments
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesFactorialMoment
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_TotalCycleVariance
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PMFToDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_ExpectedCycles
import Mathlib
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# Fixed points in a random permutation

This file records the discrete Poisson(1) limit for fixed points of a uniform
random permutation at the level currently most directly supported by Mathlib:

* the exact factorial-moment identity
  `E[(F_n)_k] = 1` for `k <= n`;
* the pointwise probability mass limit
  `P(F_n = j) -> exp(-1) / j!`.

The probability mass is expressed by the genuine derangement count
`choose n j * D_{n-j} / n!`.
-/

noncomputable section

open Filter
open scoped Topology NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace FixedPointsPoissonNS

lemma card_fixedEmbeddingsOfPerm (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype.card (FixedEmbeddingsOfPerm n k σ) =
      (fixedPointCount n σ).descFactorial k := by
  classical
  rw [← Fintype.card_congr (fixedEmbeddingsOfPermEquiv n k σ)]
  rw [Fintype.card_embedding_eq]
  simp [fixedPointCount]

lemma card_complement_embedding_range (n k : ℕ) (e : Fin k ↪ Fin n) :
    Fintype.card {x : Fin n // x ∉ Set.range e} = n - k := by
  classical
  change Fintype.card (↥((Set.range (e : Fin k → Fin n))ᶜ : Set (Fin n))) = n - k
  rw [Fintype.card_compl_set (Set.range e), Fintype.card_fin, Fintype.card_range e,
    Fintype.card_fin]

lemma card_permFixingEmbedding (n k : ℕ) (e : Fin k ↪ Fin n) :
    Fintype.card (PermFixingEmbedding n k e) = (n - k).factorial := by
  classical
  rw [← Fintype.card_congr (complementPermEquivFixingEmbedding n k e)]
  rw [Fintype.card_perm, card_complement_embedding_range n k e]

/-- Double-counting ordered fixed-point choices gives the unnormalized factorial moment. -/
theorem fixedPoint_factorialMoment_sum (n k : ℕ) :
    (∑ σ : Equiv.Perm (Fin n), (fixedPointCount n σ).descFactorial k) =
      n.descFactorial k * (n - k).factorial := by
  classical
  calc
    (∑ σ : Equiv.Perm (Fin n), (fixedPointCount n σ).descFactorial k)
        = ∑ σ : Equiv.Perm (Fin n),
            Fintype.card (FixedEmbeddingsOfPerm n k σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ _hσ
          exact (card_fixedEmbeddingsOfPerm n k σ).symm
    _ = Fintype.card (FixedEmbeddingByPerm n k) := by
          rw [Fintype.card_sigma]
    _ = Fintype.card (FixedEmbeddingByEmbedding n k) := by
          exact Fintype.card_congr (fixedEmbeddingByPermEquivByEmbedding n k)
    _ = ∑ e : Fin k ↪ Fin n, Fintype.card (PermFixingEmbedding n k e) := by
          rw [Fintype.card_sigma]
    _ = ∑ _e : Fin k ↪ Fin n, (n - k).factorial := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          exact card_permFixingEmbedding n k e
    _ = Fintype.card (Fin k ↪ Fin n) * (n - k).factorial := by
          rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = n.descFactorial k * (n - k).factorial := by
          rw [Fintype.card_embedding_eq]
          simp

/-- Exact factorial moment identity for fixed points of a uniform random permutation:
`E[(F_n)_k] = 1` for `k <= n`. -/
theorem fixedPoint_factorialMoment_eq_one {n k : ℕ} (hkn : k ≤ n) :
    uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) => ((fixedPointCount n σ).descFactorial k : ℝ)) = 1 := by
  classical
  unfold uniformPermExpectation
  have hsumNat := fixedPoint_factorialMoment_sum n k
  have hsumReal :
      (∑ σ : Equiv.Perm (Fin n), ((fixedPointCount n σ).descFactorial k : ℝ)) =
        (n.descFactorial k * (n - k).factorial : ℕ) := by
    exact_mod_cast hsumNat
  have hfacNat : n.descFactorial k * (n - k).factorial = n.factorial := by
    rw [Nat.mul_comm]
    exact Nat.factorial_mul_descFactorial hkn
  have hfacReal : ((n.descFactorial k * (n - k).factorial : ℕ) : ℝ) =
      n.factorial := by
    exact_mod_cast hfacNat
  rw [hsumReal, hfacReal]
  field_simp [Nat.factorial_ne_zero]

end FixedPointsPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
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

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
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

lemma cycleType_singleton_iff {n r : ℕ} {c : Equiv.Perm (Fin n)} :
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

lemma card_cyclesOfLength {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) :
    Fintype.card (CyclesOfLength n r) = (r - 1).factorial * n.choose r := by
  classical
  have hcycles := Equiv.Perm.card_of_cycleType_singleton
    (α := Fin n) (n := r) hr (by simpa using hrn)
  have hsub :
      Fintype.card (CyclesOfLength n r) =
        ({g | g.cycleType = ({r} : Multiset ℕ)} :
          Finset (Equiv.Perm (Fin n))).card := by
    change
      Fintype.card {c : Equiv.Perm (Fin n) // c.IsCycle ∧ c.support.card = r} =
        ({g | g.cycleType = ({r} : Multiset ℕ)} :
          Finset (Equiv.Perm (Fin n))).card
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext g
    simp [cycleType_singleton_iff]
  rw [hsub, hcycles]
  simp

lemma card_cyclesOfLengthOfPerm {n r : ℕ} (σ : Equiv.Perm (Fin n)) :
    Fintype.card (CyclesOfLengthOfPerm n r σ) = σ.cycleType.count r := by
  classical
  rw [Equiv.Perm.CycleType.count_def (σ := σ) r]
  rfl

lemma rCycleCount_eq_card_cyclesOfLengthOfPerm {n r : ℕ} (hr : 2 ≤ r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ = Fintype.card (CyclesOfLengthOfPerm n r σ) := by
  rw [card_cyclesOfLengthOfPerm]
  exact rCycleCount_eq_cycleType_count_of_ne_one (by omega : r ≠ 1) σ

lemma card_complement_cycle_support {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype.card {x : Fin n // x ∉ (c : Equiv.Perm (Fin n)).support} = n - r := by
  classical
  rw [Fintype.card_subtype_compl (fun x : Fin n => x ∈ (c : Equiv.Perm (Fin n)).support)]
  rw [Fintype.card_fin, Fintype.card_coe, c.prop.2]

lemma card_permDisjointCycle {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype.card (PermDisjointCycle c) = (n - r).factorial := by
  classical
  rw [← Fintype.card_congr (permDisjointCycleEquivComplement c)]
  rw [Fintype.card_perm, card_complement_cycle_support c]

lemma card_permContainingCycle {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype.card (PermContainingCycle c) = (n - r).factorial := by
  classical
  rw [Fintype.card_congr (permContainingCycleEquivDisjointCycle c)]
  exact card_permDisjointCycle c

theorem rCycleCount_sum_eq {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) :
    (∑ σ : Equiv.Perm (Fin n), rCycleCount n r σ) =
      (r - 1).factorial * n.choose r * (n - r).factorial := by
  classical
  calc
    (∑ σ : Equiv.Perm (Fin n), rCycleCount n r σ)
        = ∑ σ : Equiv.Perm (Fin n),
            Fintype.card (CyclesOfLengthOfPerm n r σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ _hσ
          exact rCycleCount_eq_card_cyclesOfLengthOfPerm hr σ
    _ = Fintype.card (CycleByPerm n r) := by
          rw [Fintype.card_sigma]
    _ = Fintype.card (CycleByCycle n r) := by
          exact Fintype.card_congr (cycleByPermEquivCycleByCycle n r)
    _ = ∑ c : CyclesOfLength n r, Fintype.card (PermContainingCycle c) := by
          rw [Fintype.card_sigma]
    _ = ∑ _c : CyclesOfLength n r, (n - r).factorial := by
          refine Finset.sum_congr rfl ?_
          intro c _hc
          exact card_permContainingCycle c
    _ = Fintype.card (CyclesOfLength n r) * (n - r).factorial := by
          rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = (r - 1).factorial * n.choose r * (n - r).factorial := by
          rw [card_cyclesOfLength hr hrn]

lemma r_mul_rCycleCount_sum_eq_factorial {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) :
    r * (∑ σ : Equiv.Perm (Fin n), rCycleCount n r σ) = n.factorial := by
  classical
  rw [rCycleCount_sum_eq hr hrn]
  have hr0 : r ≠ 0 := by omega
  have hfac : r.factorial = (r - 1).factorial * r := by
    rw [Nat.mul_comm, Nat.mul_factorial_pred hr0]
  calc
    r * ((r - 1).factorial * n.choose r * (n - r).factorial)
        = n.choose r * r.factorial * (n - r).factorial := by
          rw [hfac]
          ring
    _ = n.factorial := by
          exact Nat.choose_mul_factorial_mul_factorial hrn

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

theorem cycleType_count_factorialMoment_sum_in {r k : ℕ}
    (hr : 2 ≤ r) (h : r * k ≤ Fintype.card α) :
    r ^ k * (∑ σ : Equiv.Perm α, (σ.cycleType.count r).descFactorial k) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction k with
  | zero =>
      intro α _ _
      simp [Fintype.card_perm]
  | succ k ih =>
      intro α _ _ h
      have hrα : r ≤ Fintype.card α := by
        calc
          r = r * 1 := by simp
          _ ≤ r * (k + 1) := Nat.mul_le_mul_left r (Nat.succ_pos k)
          _ ≤ Fintype.card α := h
      have hrec_card :
          r * k ≤ Fintype.card α - r := by
        apply Nat.le_sub_of_add_le
        calc
          r * k + r = r * (k + 1) := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α, (σ.cycleType.count r).descFactorial (k + 1)) =
            ∑ c : CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial k := by
        calc
          (∑ σ : Equiv.Perm α, (σ.cycleType.count r).descFactorial (k + 1))
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (CyclesOfLengthOfPermIn (α := α) r σ) *
                    ((σ.cycleType.count r - 1).descFactorial k) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [card_cyclesOfLengthOfPermIn (α := α) (r := r) σ]
                rw [descFactorial_succ_eq_mul_pred]
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _c : CyclesOfLengthOfPermIn (α := α) r σ,
                    ((σ.cycleType.count r - 1).descFactorial k) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ x : CycleByPermIn (α := α) r,
                  ((x.1.cycleType.count r - 1).descFactorial k) := by
                exact (Fintype.sum_sigma'
                  (fun σ (c : CyclesOfLengthOfPermIn (α := α) r σ) =>
                    ((σ.cycleType.count r - 1).descFactorial k))).symm
          _ = ∑ x : CycleByCycleIn (α := α) r,
                  ((x.2.1.cycleType.count r - 1).descFactorial k) := by
                exact Fintype.sum_equiv (cycleByPermEquivCycleByCycleIn (α := α) r)
                  (fun x : CycleByPermIn (α := α) r =>
                    ((x.1.cycleType.count r - 1).descFactorial k))
                  (fun x : CycleByCycleIn (α := α) r =>
                    ((x.2.1.cycleType.count r - 1).descFactorial k))
                  (by intro x; rfl)
          _ = ∑ c : CyclesOfLengthIn (α := α) r,
                  ∑ σ : PermContainingCycleIn c,
                    ((σ.1.cycleType.count r - 1).descFactorial k) := by
                rw [Fintype.sum_sigma]
          _ = ∑ c : CyclesOfLengthIn (α := α) r,
                  ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial k := by
                refine Finset.sum_congr rfl ?_
                intro c _hc
                exact (Fintype.sum_equiv (permComplementEquivContainingCycleIn c)
                  (fun τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} =>
                    (τ.cycleType.count r).descFactorial k)
                  (fun σ : PermContainingCycleIn c =>
                    ((σ.1.cycleType.count r - 1).descFactorial k))
                  (by
                    intro τ
                    exact (cycleType_count_containing_from_complement (k := k) c τ).symm)).symm
      have hinner :
          ∀ c : CyclesOfLengthIn (α := α) r,
            r ^ k *
              (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial k) =
              (Fintype.card α - r).factorial := by
        intro c
        have hc_card :
            Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support} =
              Fintype.card α - r :=
          card_complement_cycle_support_in c
        have hrec :
            r ^ k *
              (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial k) =
              (Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support}).factorial :=
          ih (α := {x : α // x ∉ (c : Equiv.Perm α).support}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        r ^ (k + 1) *
            (∑ c : CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial k)
            = r * (∑ c : CyclesOfLengthIn (α := α) r,
                r ^ k *
                  (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial k)) := by
              rw [pow_succ, ← Finset.mul_sum]
              ring
        _ = r * (∑ _c : CyclesOfLengthIn (α := α) r, (Fintype.card α - r).factorial) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro c _hc
              exact hinner c
        _ = r * (Fintype.card (CyclesOfLengthIn (α := α) r) * (Fintype.card α - r).factorial) := by
              rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = (Fintype.card α).factorial := by
              rw [card_cyclesOfLengthIn (α := α) hr hrα]
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

end GeneralFinite

end FM

theorem rCycle_mean_eq_inv {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) => (rCycleCount n r σ : ℝ)) =
        (r : ℝ) ^ (-1 : ℤ) := by
  classical
  rcases eq_or_ne r 1 with rfl | hrne
  · simpa [rCycleCount, FixedPointsPoissonNS.uniformPermExpectation] using
      FixedPointsPoissonNS.fixedPoint_factorialMoment_eq_one (n := n) (k := 1) hrn
  · have hr2 : 2 ≤ r := by omega
    unfold FixedPointsPoissonNS.uniformPermExpectation
    have hsumNat := FM.r_mul_rCycleCount_sum_eq_factorial (n := n) (r := r) hr2 hrn
    have hsumReal :
        (r : ℝ) *
          (∑ σ : Equiv.Perm (Fin n), (rCycleCount n r σ : ℝ)) =
            (n.factorial : ℝ) := by
      exact_mod_cast hsumNat
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    have hnfacR : (n.factorial : ℝ) ≠ 0 := by positivity
    calc
      (∑ σ : Equiv.Perm (Fin n), (rCycleCount n r σ : ℝ)) / (n.factorial : ℝ)
          = ((n.factorial : ℝ) / (r : ℝ)) / (n.factorial : ℝ) := by
            rw [← hsumReal]
            field_simp [hrR]
      _ = (r : ℝ)⁻¹ := by
            field_simp [hrR, hnfacR]
      _ = (r : ℝ) ^ (-1 : ℤ) := by
            simp

/-- Exact factorial moment identity for the number of `r`-cycles in a uniform
permutation, stated as the finite average over `Equiv.Perm (Fin n)`.

This is the unconditional Goncharov factorial-moment identity
`E[(C_{n,r})_k] = r^{-k}` whenever `r * k ≤ n`. -/
theorem factorialMoment_rCycle {n r k : ℕ} (hr : 0 < r) (h : r * k ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) => ((rCycleCount n r σ).descFactorial k : ℝ)) =
        (r : ℝ) ^ (-(k : ℤ)) := by
  classical
  rcases eq_or_ne r 1 with rfl | hrne
  · have hkn : k ≤ n := by simpa using h
    simpa [rCycleCount, FixedPointsPoissonNS.uniformPermExpectation] using
      FixedPointsPoissonNS.fixedPoint_factorialMoment_eq_one (n := n) (k := k) hkn
  · have hr2 : 2 ≤ r := by omega
    unfold FixedPointsPoissonNS.uniformPermExpectation
    have hsum_eq :
        (∑ σ : Equiv.Perm (Fin n), (rCycleCount n r σ).descFactorial k) =
          ∑ σ : Equiv.Perm (Fin n), (σ.cycleType.count r).descFactorial k := by
      refine Finset.sum_congr rfl ?_
      intro σ _hσ
      rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    have hsumNat :
        r ^ k * (∑ σ : Equiv.Perm (Fin n), (rCycleCount n r σ).descFactorial k) =
          n.factorial := by
      rw [hsum_eq]
      simpa [Fintype.card_fin] using
        FM.cycleType_count_factorialMoment_sum_in
          (α := Fin n) (r := r) (k := k) hr2 (by simpa [Fintype.card_fin] using h)
    have hsumReal :
        (r : ℝ) ^ k *
            (∑ σ : Equiv.Perm (Fin n), ((rCycleCount n r σ).descFactorial k : ℝ)) =
          (n.factorial : ℝ) := by
      exact_mod_cast hsumNat
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    have hpowR : (r : ℝ) ^ k ≠ 0 := pow_ne_zero k hrR
    have hnfacR : (n.factorial : ℝ) ≠ 0 := by positivity
    calc
      (∑ σ : Equiv.Perm (Fin n), ((rCycleCount n r σ).descFactorial k : ℝ)) /
          (n.factorial : ℝ)
          = ((n.factorial : ℝ) / (r : ℝ) ^ k) / (n.factorial : ℝ) := by
            rw [← hsumReal]
            field_simp [hpowR]
      _ = ((r : ℝ) ^ k)⁻¹ := by
            field_simp [hpowR, hnfacR]
      _ = (r : ℝ) ^ (-(k : ℤ)) := by
            simp [zpow_neg, zpow_natCast]

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
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

/-- Exact mixed factorial-moment counting identity for two distinct nontrivial
cycle lengths on an arbitrary finite type. -/
theorem cycleType_count_two_factorialMoment_sum_in {r s a b : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r ≠ s)
    (h : r * a + s * b ≤ Fintype.card α) :
    r ^ a * s ^ b *
        (∑ σ : Equiv.Perm α,
          (σ.cycleType.count r).descFactorial a *
            (σ.cycleType.count s).descFactorial b) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction a with
  | zero =>
      intro α _ _ h
      have hsb : s * b ≤ Fintype.card α := by simpa using h
      simpa [mul_assoc] using
        FM.cycleType_count_factorialMoment_sum_in
          (α := α) (r := s) (k := b) hs hsb
  | succ a ih =>
      intro α _ _ h
      have hrα : r ≤ Fintype.card α := by
        calc
          r = r * 1 := by simp
          _ ≤ r * (a + 1) := Nat.mul_le_mul_left r (Nat.succ_pos a)
          _ ≤ Fintype.card α := by omega
      have hrec_card : r * a + s * b ≤ Fintype.card α - r := by
        apply Nat.le_sub_of_add_le
        calc
          r * a + s * b + r = r * (a + 1) + s * b := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α,
            (σ.cycleType.count r).descFactorial (a + 1) *
              (σ.cycleType.count s).descFactorial b) =
            ∑ c : FM.CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial a *
                  (τ.cycleType.count s).descFactorial b := by
        calc
          (∑ σ : Equiv.Perm α,
            (σ.cycleType.count r).descFactorial (a + 1) *
              (σ.cycleType.count s).descFactorial b)
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (FM.CyclesOfLengthOfPermIn (α := α) r σ) *
                    ((σ.cycleType.count r - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [FM.card_cyclesOfLengthOfPermIn (α := α) (r := r) σ]
                rw [FM.descFactorial_succ_eq_mul_pred]
                ring
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _c : FM.CyclesOfLengthOfPermIn (α := α) r σ,
                    ((σ.cycleType.count r - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ x : FM.CycleByPermIn (α := α) r,
                  ((x.1.cycleType.count r - 1).descFactorial a *
                    (x.1.cycleType.count s).descFactorial b) := by
                exact (Fintype.sum_sigma'
                  (fun σ (c : FM.CyclesOfLengthOfPermIn (α := α) r σ) =>
                    ((σ.cycleType.count r - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b))).symm
          _ = ∑ x : FM.CycleByCycleIn (α := α) r,
                  ((x.2.1.cycleType.count r - 1).descFactorial a *
                    (x.2.1.cycleType.count s).descFactorial b) := by
                exact Fintype.sum_equiv (FM.cycleByPermEquivCycleByCycleIn (α := α) r)
                  (fun x : FM.CycleByPermIn (α := α) r =>
                    ((x.1.cycleType.count r - 1).descFactorial a *
                      (x.1.cycleType.count s).descFactorial b))
                  (fun x : FM.CycleByCycleIn (α := α) r =>
                    ((x.2.1.cycleType.count r - 1).descFactorial a *
                      (x.2.1.cycleType.count s).descFactorial b))
                  (by intro x; rfl)
          _ = ∑ c : FM.CyclesOfLengthIn (α := α) r,
                  ∑ σ : FM.PermContainingCycleIn c,
                    ((σ.1.cycleType.count r - 1).descFactorial a *
                      (σ.1.cycleType.count s).descFactorial b) := by
                rw [Fintype.sum_sigma]
          _ = ∑ c : FM.CyclesOfLengthIn (α := α) r,
                  ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial a *
                      (τ.cycleType.count s).descFactorial b := by
                refine Finset.sum_congr rfl ?_
                intro c _hc
                exact (Fintype.sum_equiv (FM.permComplementEquivContainingCycleIn c)
                  (fun τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} =>
                    (τ.cycleType.count r).descFactorial a *
                      (τ.cycleType.count s).descFactorial b)
                  (fun σ : FM.PermContainingCycleIn c =>
                    ((σ.1.cycleType.count r - 1).descFactorial a *
                      (σ.1.cycleType.count s).descFactorial b))
                  (by
                    intro τ
                    change
                      (τ.cycleType.count r).descFactorial a *
                          (τ.cycleType.count s).descFactorial b =
                        ((((FM.permComplementEquivContainingCycleIn c) τ).1.cycleType.count r -
                            1).descFactorial a *
                          (((FM.permComplementEquivContainingCycleIn c) τ).1.cycleType.count s).descFactorial b)
                    rw [← FM.cycleType_count_containing_from_complement (k := a) c τ]
                    rw [← cycleType_count_containing_from_complement_ne (α := α)
                      (s := s) (r := r) (Ne.symm hrs) c τ])).symm
      have hinner :
          ∀ c : FM.CyclesOfLengthIn (α := α) r,
            r ^ a * s ^ b *
                (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                  (τ.cycleType.count r).descFactorial a *
                    (τ.cycleType.count s).descFactorial b) =
              (Fintype.card α - r).factorial := by
        intro c
        have hc_card :
            Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support} =
              Fintype.card α - r :=
          FM.card_complement_cycle_support_in c
        have hrec :
            r ^ a * s ^ b *
                (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                  (τ.cycleType.count r).descFactorial a *
                    (τ.cycleType.count s).descFactorial b) =
              (Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support}).factorial :=
          ih (α := {x : α // x ∉ (c : Equiv.Perm α).support}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        r ^ (a + 1) * s ^ b *
            (∑ c : FM.CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial a *
                  (τ.cycleType.count s).descFactorial b)
            = r * (∑ c : FM.CyclesOfLengthIn (α := α) r,
                r ^ a * s ^ b *
                  (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial a *
                      (τ.cycleType.count s).descFactorial b)) := by
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

/-- Exact mixed factorial-moment counting identity for fixed points and one
nontrivial cycle length on an arbitrary finite type. -/
theorem fixedPoint_cycleType_count_factorialMoment_sum_in {s a b : ℕ}
    (hs : 2 ≤ s) (h : a + s * b ≤ Fintype.card α) :
    s ^ b *
        (∑ σ : Equiv.Perm α,
          (fixedPointCountIn σ).descFactorial a *
            (σ.cycleType.count s).descFactorial b) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction a with
  | zero =>
      intro α _ _ h
      have hsb : s * b ≤ Fintype.card α := by simpa using h
      simpa [fixedPointCountIn, mul_assoc] using
        FM.cycleType_count_factorialMoment_sum_in
          (α := α) (r := s) (k := b) hs hsb
  | succ a ih =>
      intro α _ _ h
      have hcard0 : Fintype.card α ≠ 0 := by omega
      have hrec_card : a + s * b ≤ Fintype.card α - 1 := by
        apply Nat.le_sub_of_add_le
        calc
          a + s * b + 1 = a + 1 + s * b := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α,
            (fixedPointCountIn σ).descFactorial (a + 1) *
              (σ.cycleType.count s).descFactorial b) =
            ∑ x : α,
              ∑ τ : Equiv.Perm {y : α // y ≠ x},
                (fixedPointCountIn τ).descFactorial a *
                  (τ.cycleType.count s).descFactorial b := by
        calc
          (∑ σ : Equiv.Perm α,
            (fixedPointCountIn σ).descFactorial (a + 1) *
              (σ.cycleType.count s).descFactorial b)
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (FixedPointsOfPermIn (α := α) σ) *
                    ((fixedPointCountIn σ - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [fixedPointCountIn]
                rw [FM.descFactorial_succ_eq_mul_pred]
                ring
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _x : FixedPointsOfPermIn (α := α) σ,
                    ((fixedPointCountIn σ - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ z : FixedPointByPermIn (α := α),
                  ((fixedPointCountIn z.1 - 1).descFactorial a *
                    (z.1.cycleType.count s).descFactorial b) := by
                exact (Fintype.sum_sigma'
                  (fun σ (_x : FixedPointsOfPermIn (α := α) σ) =>
                    ((fixedPointCountIn σ - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b))).symm
          _ = ∑ z : FixedPointByPointIn (α := α),
                  ((fixedPointCountIn z.2.1 - 1).descFactorial a *
                    (z.2.1.cycleType.count s).descFactorial b) := by
                exact Fintype.sum_equiv (fixedPointByPermEquivByPointIn (α := α))
                  (fun z : FixedPointByPermIn (α := α) =>
                    ((fixedPointCountIn z.1 - 1).descFactorial a *
                      (z.1.cycleType.count s).descFactorial b))
                  (fun z : FixedPointByPointIn (α := α) =>
                    ((fixedPointCountIn z.2.1 - 1).descFactorial a *
                      (z.2.1.cycleType.count s).descFactorial b))
                  (by intro z; rfl)
          _ = ∑ x : α,
                  ∑ σ : PermFixingPointIn (α := α) x,
                    ((fixedPointCountIn σ.1 - 1).descFactorial a *
                      (σ.1.cycleType.count s).descFactorial b) := by
                rw [Fintype.sum_sigma]
          _ = ∑ x : α,
                  ∑ τ : Equiv.Perm {y : α // y ≠ x},
                    (fixedPointCountIn τ).descFactorial a *
                      (τ.cycleType.count s).descFactorial b := by
                refine Finset.sum_congr rfl ?_
                intro x _hx
                exact (Fintype.sum_equiv (permComplementEquivFixingPointIn x)
                  (fun τ : Equiv.Perm {y : α // y ≠ x} =>
                    (fixedPointCountIn τ).descFactorial a *
                      (τ.cycleType.count s).descFactorial b)
                  (fun σ : PermFixingPointIn (α := α) x =>
                    ((fixedPointCountIn σ.1 - 1).descFactorial a *
                      (σ.1.cycleType.count s).descFactorial b))
                  (by
                    intro τ
                    change
                      (fixedPointCountIn τ).descFactorial a *
                          (τ.cycleType.count s).descFactorial b =
                        ((fixedPointCountIn ((permComplementEquivFixingPointIn x) τ).1 -
                            1).descFactorial a *
                          (((permComplementEquivFixingPointIn x) τ).1.cycleType.count s).descFactorial b)
                    rw [← fixedPointCount_fixingPoint_from_complement_desc (α := α) x τ]
                    rw [← cycleType_count_fixingPoint_from_complement (α := α)
                      (s := s) x τ])).symm
      have hinner :
          ∀ x : α,
            s ^ b *
                (∑ τ : Equiv.Perm {y : α // y ≠ x},
                  (fixedPointCountIn τ).descFactorial a *
                    (τ.cycleType.count s).descFactorial b) =
              (Fintype.card α - 1).factorial := by
        intro x
        have hc_card :
            Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 :=
          card_complement_point x
        have hrec :
            s ^ b *
                (∑ τ : Equiv.Perm {y : α // y ≠ x},
                  (fixedPointCountIn τ).descFactorial a *
                    (τ.cycleType.count s).descFactorial b) =
              (Fintype.card {y : α // y ≠ x}).factorial :=
          ih (α := {y : α // y ≠ x}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        s ^ b *
            (∑ x : α,
              ∑ τ : Equiv.Perm {y : α // y ≠ x},
                (fixedPointCountIn τ).descFactorial a *
                  (τ.cycleType.count s).descFactorial b)
            = ∑ x : α,
                s ^ b *
                  (∑ τ : Equiv.Perm {y : α // y ≠ x},
                    (fixedPointCountIn τ).descFactorial a *
                      (τ.cycleType.count s).descFactorial b) := by
              rw [Finset.mul_sum]
        _ = ∑ _x : α, (Fintype.card α - 1).factorial := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              exact hinner x
        _ = Fintype.card α * (Fintype.card α - 1).factorial := by
              rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = (Fintype.card α).factorial := by
              exact Nat.mul_factorial_pred hcard0

end GeneralFinite

/-- Exact mixed factorial-moment counting identity for two distinct nontrivial
cycle lengths in permutations of `Fin n`, stated using the genuine
`rCycleCount` variables. -/
theorem rCycleCount_two_factorialMoment_sum {n r s a b : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r ≠ s)
    (h : r * a + s * b ≤ n) :
    r ^ a * s ^ b *
        (∑ σ : Equiv.Perm (Fin n),
          (rCycleCount n r σ).descFactorial a *
            (rCycleCount n s σ).descFactorial b) =
      n.factorial := by
  classical
  have hrne : r ≠ 1 := by omega
  have hsne : s ≠ 1 := by omega
  have hsum_eq :
      (∑ σ : Equiv.Perm (Fin n),
        (rCycleCount n r σ).descFactorial a *
          (rCycleCount n s σ).descFactorial b) =
        ∑ σ : Equiv.Perm (Fin n),
          (σ.cycleType.count r).descFactorial a *
            (σ.cycleType.count s).descFactorial b := by
    refine Finset.sum_congr rfl ?_
    intro σ _hσ
    rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    rw [rCycleCount_eq_cycleType_count_of_ne_one hsne σ]
  rw [hsum_eq]
  simpa [Fintype.card_fin] using
    cycleType_count_two_factorialMoment_sum_in
      (α := Fin n) (r := r) (s := s) (a := a) (b := b)
      hr hs hrs (by simpa [Fintype.card_fin] using h)

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

/-- Exact mixed factorial-moment counting identity for fixed points and one
nontrivial cycle length, stated using `rCycleCount n 1` and `rCycleCount n s`. -/
theorem rCycleCount_one_two_factorialMoment_sum {n s a b : ℕ}
    (hs : 2 ≤ s) (h : a + s * b ≤ n) :
    s ^ b *
        (∑ σ : Equiv.Perm (Fin n),
          (rCycleCount n 1 σ).descFactorial a *
            (rCycleCount n s σ).descFactorial b) =
      n.factorial := by
  classical
  have hsne : s ≠ 1 := by omega
  have hsum_eq :
      (∑ σ : Equiv.Perm (Fin n),
        (rCycleCount n 1 σ).descFactorial a *
          (rCycleCount n s σ).descFactorial b) =
        ∑ σ : Equiv.Perm (Fin n),
          (fixedPointCountIn σ).descFactorial a *
            (σ.cycleType.count s).descFactorial b := by
    refine Finset.sum_congr rfl ?_
    intro σ _hσ
    rw [rCycleCount_one]
    rw [rCycleCount_eq_cycleType_count_of_ne_one hsne σ]
    rw [fixedPointCountIn_fin n σ]
  rw [hsum_eq]
  simpa [Fintype.card_fin] using
    fixedPoint_cycleType_count_factorialMoment_sum_in
      (α := Fin n) (s := s) (a := a) (b := b) hs
      (by simpa [Fintype.card_fin] using h)

/-- Exact mixed factorial moment for two distinct nontrivial cycle lengths. -/
theorem factorialMoment_two_rCycle {n r s a b : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r ≠ s)
    (h : r * a + s * b ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (r : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
  classical
  unfold FixedPointsPoissonNS.uniformPermExpectation
  have hsumNat :=
    rCycleCount_two_factorialMoment_sum
      (n := n) (r := r) (s := s) (a := a) (b := b) hr hs hrs h
  have hsumReal :
      (r : ℝ) ^ a * (s : ℝ) ^ b *
          (∑ σ : Equiv.Perm (Fin n),
            ((rCycleCount n r σ).descFactorial a : ℝ) *
              ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (n.factorial : ℝ) := by
    exact_mod_cast hsumNat
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < r))
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < s))
  have hpowR : (r : ℝ) ^ a * (s : ℝ) ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero a hrR) (pow_ne_zero b hsR)
  have hnfacR : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    (∑ σ : Equiv.Perm (Fin n),
          ((rCycleCount n r σ).descFactorial a : ℝ) *
            ((rCycleCount n s σ).descFactorial b : ℝ)) /
        (n.factorial : ℝ)
        = ((n.factorial : ℝ) / ((r : ℝ) ^ a * (s : ℝ) ^ b)) /
            (n.factorial : ℝ) := by
          rw [← hsumReal]
          field_simp [hpowR]
    _ = (((r : ℝ) ^ a * (s : ℝ) ^ b)⁻¹) := by
          field_simp [hpowR, hnfacR]
    _ = (r : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
          simp [zpow_neg, zpow_natCast, mul_comm]

/-- Exact mixed factorial moment for fixed points and one nontrivial cycle
length, stated using the genuine `rCycleCount` variables. -/
theorem factorialMoment_one_and_rCycle {n s a b : ℕ}
    (hs : 2 ≤ s) (h : a + s * b ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ((rCycleCount n 1 σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (1 : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
  classical
  unfold FixedPointsPoissonNS.uniformPermExpectation
  have hsumNat :=
    rCycleCount_one_two_factorialMoment_sum
      (n := n) (s := s) (a := a) (b := b) hs h
  have hsumReal :
      (s : ℝ) ^ b *
          (∑ σ : Equiv.Perm (Fin n),
            ((rCycleCount n 1 σ).descFactorial a : ℝ) *
              ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (n.factorial : ℝ) := by
    exact_mod_cast hsumNat
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < s))
  have hpowR : (s : ℝ) ^ b ≠ 0 := pow_ne_zero b hsR
  have hnfacR : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    (∑ σ : Equiv.Perm (Fin n),
          ((rCycleCount n 1 σ).descFactorial a : ℝ) *
            ((rCycleCount n s σ).descFactorial b : ℝ)) /
        (n.factorial : ℝ)
        = ((n.factorial : ℝ) / (s : ℝ) ^ b) / (n.factorial : ℝ) := by
          rw [← hsumReal]
          field_simp [hpowR]
    _ = ((s : ℝ) ^ b)⁻¹ := by
          field_simp [hpowR, hnfacR]
    _ = (1 : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
          simp [zpow_neg, zpow_natCast]

/-- Unified exact mixed factorial moment for two distinct positive cycle
lengths.  This combines the nontrivial/nontrivial case with the fixed-point
branch for length `1`. -/
theorem factorialMoment_two_rCycle_of_pos {n r s a b : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s)
    (h : r * a + s * b ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (r : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
  classical
  rcases eq_or_ne r 1 with rfl | hrne
  · have hs2 : 2 ≤ s := by omega
    simpa using
      factorialMoment_one_and_rCycle
        (n := n) (s := s) (a := a) (b := b) hs2 (by simpa using h)
  · have hr2 : 2 ≤ r := by omega
    rcases eq_or_ne s 1 with rfl | hsne
    · have h' : b + r * a ≤ n := by omega
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        factorialMoment_one_and_rCycle
          (n := n) (s := r) (a := b) (b := a) hr2 h'
    · have hs2 : 2 ≤ s := by omega
      exact factorialMoment_two_rCycle
        (n := n) (r := r) (s := s) (a := a) (b := b) hr2 hs2 hrs h

end JointCycleMomentsNS
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
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

end Complete
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
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

lemma Multiset.count_two_mul_le_sum (r s : ℕ) (hrs : r ≠ s) :
    ∀ m : Multiset ℕ, m.count r * r + m.count s * s ≤ m.sum := by
  intro m
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | cons a m ih =>
      by_cases har : a = r
      · subst a
        have hsr : s ≠ r := Ne.symm hrs
        simp [hsr, Multiset.sum_cons, Nat.succ_mul]
        omega
      · by_cases has : a = s
        · subst a
          simp [hrs, Multiset.sum_cons, Nat.succ_mul]
          omega
        · have hle : m.count r * r + m.count s * s ≤ a + m.sum :=
            Nat.le_trans ih (Nat.le_add_left _ _)
          have hra : r ≠ a := fun h => har h.symm
          have hsa : s ≠ a := fun h => has h.symm
          simpa [Multiset.count_cons, hra, hsa, Multiset.sum_cons] using hle

lemma rCycleCount_one_eq_card_sub_cycleType_sum (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n 1 σ = n - σ.cycleType.sum := by
  rw [rCycleCount_one]
  rw [← JointCycleMomentsNS.fixedPointCountIn_fin n σ]
  rw [JointCycleMomentsNS.fixedPointCountIn]
  rw [Equiv.Perm.card_fixedPoints]
  simp [Fintype.card_fin]

/-- Joint support bound: cycles of two distinct positive lengths use at most `n` labels. -/
lemma joint_rCycleCount_weight_le_card {n r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) (σ : Equiv.Perm (Fin n)) :
    r * rCycleCount n r σ + s * rCycleCount n s σ ≤ n := by
  classical
  rcases eq_or_ne r 1 with rfl | hrne
  · have hsne : s ≠ 1 := by
      intro hs1
      exact hrs hs1.symm
    have hs_count :
        s * rCycleCount n s σ ≤ σ.cycleType.sum := by
      rw [rCycleCount_eq_cycleType_count_of_ne_one hsne σ]
      simpa [Nat.mul_comm] using
        Complete.Multiset.count_mul_le_sum s σ.cycleType
    have hfixed := rCycleCount_one_eq_card_sub_cycleType_sum n σ
    calc
      1 * rCycleCount n 1 σ + s * rCycleCount n s σ
          = (n - σ.cycleType.sum) + s * rCycleCount n s σ := by
            rw [hfixed]
            simp
      _ ≤ (n - σ.cycleType.sum) + σ.cycleType.sum := by
            exact Nat.add_le_add_left hs_count _
      _ = n := by
            exact Nat.sub_add_cancel (by
              simpa [Fintype.card_fin] using Equiv.Perm.sum_cycleType_le σ)
  · rcases eq_or_ne s 1 with rfl | hsne
    · have hr_count :
          r * rCycleCount n r σ ≤ σ.cycleType.sum := by
        rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
        simpa [Nat.mul_comm] using
          Complete.Multiset.count_mul_le_sum r σ.cycleType
      have hfixed := rCycleCount_one_eq_card_sub_cycleType_sum n σ
      calc
        r * rCycleCount n r σ + 1 * rCycleCount n 1 σ
            = r * rCycleCount n r σ + (n - σ.cycleType.sum) := by
              rw [hfixed]
              simp
        _ ≤ σ.cycleType.sum + (n - σ.cycleType.sum) := by
              exact Nat.add_le_add_right hr_count _
        _ = n := by
              rw [Nat.add_comm]
              exact Nat.sub_add_cancel (by
                simpa [Fintype.card_fin] using Equiv.Perm.sum_cycleType_le σ)
    · have htwo :
          r * rCycleCount n r σ + s * rCycleCount n s σ ≤ σ.cycleType.sum := by
        rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
        rw [rCycleCount_eq_cycleType_count_of_ne_one hsne σ]
        simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Multiset.count_two_mul_le_sum r s hrs σ.cycleType
      exact htwo.trans (by
        simpa [Fintype.card_fin] using Equiv.Perm.sum_cycleType_le σ)

lemma joint_factorial_moment_zero_of_lt {n r s a b : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) (h : n < r * a + s * b) :
    (∑ σ : Equiv.Perm (Fin n),
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) /
      (n.factorial : ℝ) = 0 := by
  classical
  suffices
      (∑ σ : Equiv.Perm (Fin n),
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) = 0 by
    rw [this]
    simp
  refine Finset.sum_eq_zero ?_
  intro σ _hσ
  by_cases ha : a ≤ rCycleCount n r σ
  · by_cases hb : b ≤ rCycleCount n s σ
    · have huse :
          r * a + s * b ≤
            r * rCycleCount n r σ + s * rCycleCount n s σ := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left r ha) (Nat.mul_le_mul_left s hb)
      have hcard := joint_rCycleCount_weight_le_card (n := n) (r := r) (s := s)
        hr hs hrs σ
      have : r * a + s * b ≤ n := huse.trans hcard
      omega
    · have hbzero : (rCycleCount n s σ).descFactorial b = 0 :=
        (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_of_not_ge hb)
      simp [hbzero]
  · have hazero : (rCycleCount n r σ).descFactorial a = 0 :=
      (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_of_not_ge ha)
    simp [hazero]

/-- If two distinct cycle lengths fit together, their product moment is the product
of the two means. -/
theorem joint_product_expectation_eq_inv_mul_inv_of_le {n r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (h : r + s ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) =
        (r : ℝ)⁻¹ * (s : ℝ)⁻¹ := by
  have hmom := JointCycleMomentsNS.factorialMoment_two_rCycle_of_pos
    (n := n) (r := r) (s := s) (a := 1) (b := 1) hr hs hrs (by simpa using h)
  simpa [FixedPointsPoissonNS.uniformPermExpectation, Nat.descFactorial_one, zpow_neg_one]
    using hmom

/-- If the two requested cycle lengths do not both fit, then the product moment is zero. -/
theorem joint_product_expectation_eq_zero_of_lt {n r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (h : n < r + s) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) = 0 := by
  have hzero := joint_factorial_moment_zero_of_lt
    (n := n) (r := r) (s := s) (a := 1) (b := 1) hr hs hrs (by simpa using h)
  simpa [FixedPointsPoissonNS.uniformPermExpectation, Nat.descFactorial_one] using hzero

end Bivariate
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
/-!
# Variance of the number of `r`-cycles

From the banked factorial moments `E[(C_{n,r})_1] = 1/r` and `E[(C_{n,r})_2] = 1/r²`
(`rCycle_mean_eq_inv`, `factorialMoment_rCycle`), the variance of the number of length-`r`
cycles in a uniform random permutation is

  `Var(C_{n,r}) = E[(C_{n,r})_2] + E[C_{n,r}] - (E[C_{n,r}])² = 1/r² + 1/r - 1/r² = 1/r`,

for `2r ≤ n`.  This matches the variance `1/r` of the Poisson(1/r) limit, a second-moment
confirmation of `rCycles_tendstoInDistribution_poisson`.
-/

noncomputable section

open scoped BigOperators

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- The pointwise identity `k² = (k)_2 + k` in `ℕ` (`(k)_2 = k(k-1)`). -/
lemma sq_eq_descFactorial_two_add (k : ℕ) : k ^ 2 = k.descFactorial 2 + k := by
  have hdf : k.descFactorial 2 = (k - 1) * k := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
  rw [hdf]
  cases k with
  | zero => rfl
  | succ m => simp only [Nat.succ_sub_one]; ring

/-- `E[X²]` splits as `E[(X)_2] + E[X]` for the `r`-cycle count (linearity of the average). -/
lemma uniformPermExpectation_sq_eq (n r : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) =
      FixedPointsPoissonNS.uniformPermExpectation n
          (fun σ => ((rCycleCount n r σ).descFactorial 2 : ℝ)) +
        FixedPointsPoissonNS.uniformPermExpectation n
          (fun σ => (rCycleCount n r σ : ℝ)) := by
  unfold FixedPointsPoissonNS.uniformPermExpectation
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro σ _
  have hnat : (rCycleCount n r σ) ^ 2 =
      (rCycleCount n r σ).descFactorial 2 + rCycleCount n r σ :=
    sq_eq_descFactorial_two_add _
  have := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at this ⊢
  linarith [this]

lemma sq_eq_self_of_le_one (k : ℕ) (hk : k ≤ 1) : k ^ 2 = k := by
  interval_cases k <;> norm_num

lemma rCycleCount_le_one_of_large {n r : ℕ} (hr : 0 < r) (hlarge : n < 2 * r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ ≤ 1 := by
  by_contra hle
  have htwo : 2 ≤ rCycleCount n r σ := by omega
  have hmul : 2 * r ≤ rCycleCount n r σ * r :=
    Nat.mul_le_mul_right r htwo
  have hcard := Complete.rCycleCount_mul_le_card (n := n) (r := r) hr σ
  exact (not_le_of_gt hlarge) (hmul.trans hcard)

/-- The finite second moment of the number of `r`-cycles is `1/r + 1/r²` when
there is room for two disjoint `r`-cycles. -/
theorem rCycle_second_moment_eq_inv_add_inv_sq {n r : ℕ} (hr : 0 < r) (h2 : 2 * r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) =
      (r : ℝ)⁻¹ + ((r : ℝ)⁻¹) ^ 2 := by
  have hrn : r ≤ n := by omega
  have hk2 : r * 2 ≤ n := by omega
  have hmean :
      FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ)) = (r : ℝ)⁻¹ := by
    rw [rCycle_mean_eq_inv hr hrn]; simp
  have key : (r : ℝ) ^ (-((2 : ℕ) : ℤ)) = ((r : ℝ)⁻¹) ^ 2 := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
  rw [uniformPermExpectation_sq_eq, hmean, factorialMoment_rCycle hr hk2, key]
  ring

/-- If a cycle of length `r` fits but two such cycles cannot fit, then `C_{n,r}`
is pointwise a `0/1` random variable, so its second moment equals its mean. -/
theorem rCycle_second_moment_eq_inv_of_large {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    (hlarge : n < 2 * r) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) = (r : ℝ)⁻¹ := by
  have hpoint :
      (fun σ : Equiv.Perm (Fin n) => (rCycleCount n r σ : ℝ) ^ 2) =
        fun σ => (rCycleCount n r σ : ℝ) := by
    funext σ
    have hsq :
        (rCycleCount n r σ) ^ 2 = rCycleCount n r σ :=
      sq_eq_self_of_le_one _ (rCycleCount_le_one_of_large hr hlarge σ)
    exact_mod_cast hsq
  rw [hpoint, rCycle_mean_eq_inv hr hrn]
  simp

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
/-!
# Expected number of cycles of a random permutation

The total number of cycles (orbits, including fixed points) of a permutation of `Fin n` is
`∑_{r=1}^{n} C_{n,r}`, where `C_{n,r} = rCycleCount n r` is the number of length-`r` cycles.
Summing the banked per-length means `E[C_{n,r}] = 1/r` (`rCycle_mean_eq_inv`) over `r = 1,…,n` by
linearity of expectation gives the classical identity

  `E[#cycles] = ∑_{r=1}^{n} 1/r = H_n`,

the `n`-th harmonic number.  (Asymptotically `H_n ∼ log n`, recovering the Goncharov result that a
uniform random permutation has about `log n` cycles.)

This is a genuine consequence of the factorial-moment machinery, not a Mathlib re-statement.
-/

noncomputable section

open Filter
open scoped BigOperators

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- Linearity of the uniform permutation expectation over a finite sum of random variables. -/
lemma uniformPermExpectation_finset_sum (n : ℕ) (S : Finset ℕ)
    (g : ℕ → Equiv.Perm (Fin n) → ℝ) :
    FixedPointsPoissonNS.uniformPermExpectation n (fun σ => ∑ r ∈ S, g r σ) =
      ∑ r ∈ S, FixedPointsPoissonNS.uniformPermExpectation n (fun σ => g r σ) := by
  unfold FixedPointsPoissonNS.uniformPermExpectation
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]

/-- Linearity of the uniform permutation expectation over a finite double sum. -/
lemma uniformPermExpectation_finset_sum₂ (n : ℕ) (S T : Finset ℕ)
    (g : ℕ → ℕ → Equiv.Perm (Fin n) → ℝ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => ∑ r ∈ S, ∑ s ∈ T, g r s σ) =
      ∑ r ∈ S, ∑ s ∈ T,
        FixedPointsPoissonNS.uniformPermExpectation n (fun σ => g r s σ) := by
  rw [uniformPermExpectation_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [uniformPermExpectation_finset_sum]

/-- **Expected number of cycles of a uniform random permutation is the harmonic number.**
`E[ ∑_{r=1}^{n} C_{n,r} ] = ∑_{r=1}^{n} 1/r`. -/
theorem expected_totalCycles_eq_harmonic (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ => (totalCycleCount n σ : ℝ)) =
        ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ := by
  have hcast :
      (fun σ : Equiv.Perm (Fin n) => (totalCycleCount n σ : ℝ)) =
        fun σ => ∑ r ∈ Finset.Icc 1 n, ((rCycleCount n r σ : ℝ)) := by
    funext σ
    unfold totalCycleCount
    push_cast
    rfl
  rw [hcast, uniformPermExpectation_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_Icc] at hr
  have hpos : 0 < r := hr.1
  have hle : r ≤ n := hr.2
  rw [rCycle_mean_eq_inv hpos hle]
  simp

/-- Expanding the square of the total cycle count reduces its second moment to
the matrix of two-length product moments. -/
theorem expected_totalCycles_sq_eq_sum_products (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) =
      ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
        FixedPointsPoissonNS.uniformPermExpectation n
          (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) := by
  have hpoint :
      (fun σ : Equiv.Perm (Fin n) => (totalCycleCount n σ : ℝ) ^ 2) =
        fun σ =>
          ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
            (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ) := by
    funext σ
    unfold totalCycleCount
    push_cast
    rw [pow_two, Finset.sum_mul_sum]
  rw [hpoint, uniformPermExpectation_finset_sum₂]

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
/-!
# Second moment matrix for the total number of cycles

This file assembles the diagonal and off-diagonal cycle-count moment bricks into
a single finite matrix formula for the second moment of the total number of
cycles in a uniform random permutation.
-/

noncomputable section

open scoped BigOperators

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- Unified finite product-moment formula for two cycle lengths that separately fit in `Fin n`.

The first summand is the diagonal Bernoulli/counting contribution; the second
summand is present exactly when cycles of lengths `r` and `s` can coexist. -/
theorem cycle_product_moment_eq_diag_add_fit {n r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrn : r ≤ n) (hsn : s ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) =
      (if r = s then (r : ℝ)⁻¹ else 0) +
        if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0 := by
  by_cases hrs : r = s
  · subst s
    by_cases hfit : r + r ≤ n
    · have h2 : 2 * r ≤ n := by omega
      have hsqfun :
          (fun σ : Equiv.Perm (Fin n) =>
              (rCycleCount n r σ : ℝ) * (rCycleCount n r σ : ℝ)) =
            fun σ => (rCycleCount n r σ : ℝ) ^ 2 := by
        funext σ
        ring
      rw [hsqfun, if_pos rfl, if_pos hfit, rCycle_second_moment_eq_inv_add_inv_sq hr h2]
      ring
    · have hlarge : n < 2 * r := by omega
      have hsqfun :
          (fun σ : Equiv.Perm (Fin n) =>
              (rCycleCount n r σ : ℝ) * (rCycleCount n r σ : ℝ)) =
            fun σ => (rCycleCount n r σ : ℝ) ^ 2 := by
        funext σ
        ring
      rw [hsqfun, if_pos rfl, if_neg hfit, rCycle_second_moment_eq_inv_of_large hr hrn hlarge]
      simp
  · by_cases hfit : r + s ≤ n
    · rw [if_neg hrs, if_pos hfit,
        Bivariate.joint_product_expectation_eq_inv_mul_inv_of_le hr hs hrs hfit]
      simp
    · have htail : n < r + s := Nat.lt_of_not_ge hfit
      rw [if_neg hrs, if_neg hfit,
        Bivariate.joint_product_expectation_eq_zero_of_lt hr hs hrs htail]
      simp

/-- The total cycle-count second moment as a finite matrix with diagonal and coexistence terms. -/
theorem expected_totalCycles_sq_eq_diag_add_fit_sum (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) =
      ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
        ((if r = s then (r : ℝ)⁻¹ else 0) +
          if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0) := by
  rw [expected_totalCycles_sq_eq_sum_products]
  refine Finset.sum_congr rfl ?_
  intro r hrmem
  refine Finset.sum_congr rfl ?_
  intro s hsmem
  rw [Finset.mem_Icc] at hrmem hsmem
  exact cycle_product_moment_eq_diag_add_fit hrmem.1 hsmem.1 hrmem.2 hsmem.2

/-- The ordered pair contribution from cycle lengths that can coexist. -/
def cycleFitPairSum (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
    if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0

lemma sum_diag_indicator_Icc (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
      if r = s then (r : ℝ)⁻¹ else 0) =
        ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ := by
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _hs hsr
    simp [hsr.symm]
  · intro hnot
    exact False.elim (hnot hr)

/-- The total second moment split into the harmonic diagonal and the coexistence pair sum. -/
theorem expected_totalCycles_sq_eq_harmonic_add_fitPairSum (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) =
      (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹) + cycleFitPairSum n := by
  rw [expected_totalCycles_sq_eq_diag_add_fit_sum, cycleFitPairSum]
  simp_rw [Finset.sum_add_distrib]
  rw [sum_diag_indicator_Icc]

/-- Variance of the total cycle count reduced to a finite harmonic/pair-sum identity. -/
theorem totalCycleCount_variance_eq_harmonic_add_fitPairSum_sub_sq (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) -
      (FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ))) ^ 2 =
      (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹) + cycleFitPairSum n -
        (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹) ^ 2 := by
  rw [expected_totalCycles_sq_eq_harmonic_add_fitPairSum, expected_totalCycles_eq_harmonic]

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

/-!
# Exact variance of the total number of cycles in a uniform random permutation

The Goncharov–Kolchin companion to the cycle-count CLT: for `K_n` the total number of cycles of a
uniform random permutation of `[n]`,

  `E[K_n] = H_n`,   `Var(K_n) = H_n − H_n^{(2)}`,

where `H_n = ∑_{r=1}^n 1/r` and `H_n^{(2)} = ∑_{r=1}^n 1/r²`.

`TotalCycleSecondMoment` already reduces the variance to `H_n + cycleFitPairSum n − H_n²`.  This file
supplies the one remaining finite identity `cycleFitPairSum n = H_n² − H_n^{(2)}` (antidiagonal split
`1/(r(n+1−r)) = (1/r + 1/(n+1−r))/(n+1)` plus the reflection `r ↦ n+1−r`), giving the exact variance.
-/

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

lemma cycleH1_succ (n : ℕ) :
    cycleH1 (n + 1) = cycleH1 n + ((n + 1 : ℕ) : ℝ)⁻¹ := by
  unfold cycleH1
  rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
        ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp [Finset.mem_Icc])]
  ring

lemma cycleH2_succ (n : ℕ) :
    cycleH2 (n + 1) = cycleH2 n + (((n + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
  unfold cycleH2
  rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
        ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp [Finset.mem_Icc])]
  ring

/-- The one nontrivial finite-set rearrangement: peeling level `n+1` off `cycleFitPairSum`. -/
lemma cycleFitPairSum_succ (n : ℕ) :
    cycleFitPairSum (n + 1)
      = cycleFitPairSum n
        + ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹) := by
  classical
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 (n + 1) := by
    intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  -- Step 1: the `n+1` row and column carry zero mass; reduce both sums to `Icc 1 n`.
  have hreduce :
      cycleFitPairSum (n + 1)
        = ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
            (if r + s ≤ n + 1 then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0) := by
    unfold cycleFitPairSum
    refine (Finset.sum_subset hsub ?_).symm.trans ?_
    · intro r hr hrn
      rw [Finset.mem_Icc] at hr; rw [Finset.mem_Icc] at hrn
      apply Finset.sum_eq_zero; intro s hs
      rw [Finset.mem_Icc] at hs; rw [if_neg (by omega)]
    · apply Finset.sum_congr rfl; intro r hr
      rw [Finset.mem_Icc] at hr
      refine (Finset.sum_subset hsub ?_).symm
      intro s hs hsn
      rw [Finset.mem_Icc] at hs; rw [Finset.mem_Icc] at hsn
      rw [if_neg (by omega)]
  -- Step 2: split `[r+s ≤ n+1] = [r+s ≤ n] + [r+s = n+1]` termwise.
  have hsplit :
      (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
          (if r + s ≤ n + 1 then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0))
        = (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
            ((if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0)
              + (if r + s = n + 1 then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0))) := by
    apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _
    by_cases h1 : r + s ≤ n
    · rw [if_pos h1, if_pos (by omega), if_neg (by omega), add_zero]
    · by_cases h2 : r + s = n + 1
      · rw [if_neg h1, if_pos (by omega), if_pos h2, zero_add]
      · rw [if_neg h1, if_neg (by omega), if_neg h2, add_zero]
  -- boundary collapses to the antidiagonal
  have hbdry :
      (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
          (if r + s = n + 1 then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0))
        = ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_congr rfl; intro r hr; rw [Finset.mem_Icc] at hr
    rw [Finset.sum_eq_single_of_mem (n + 1 - r) (Finset.mem_Icc.mpr (by omega))]
    · rw [if_pos (by omega)]
    · intro s _ hsne; rw [if_neg (by omega)]
  have hAeq :
      (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
          (if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0)) = cycleFitPairSum n := rfl
  rw [hreduce, hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [hAeq, hbdry]

/-- Antidiagonal splitting of a reciprocal product on the line `r + s = n+1`. -/
lemma inv_boundary_point {n r : ℕ} (hr : r ∈ Finset.Icc 1 n) :
    (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹)
      = (((r : ℝ)⁻¹) + (((n + 1 - r : ℕ) : ℝ)⁻¹)) / ((n + 1 : ℕ) : ℝ) := by
  rw [Finset.mem_Icc] at hr
  have hcast : ((n + 1 - r : ℕ) : ℝ) = (n : ℝ) + 1 - r := by
    rw [Nat.cast_sub (by omega : r ≤ n + 1)]; push_cast; ring
  have hNR : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, hNR]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 - r := by
    have : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr.2
    linarith
  have hnrR : ((n : ℝ) + 1 - r) ≠ 0 := ne_of_gt hpos
  have hN1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Reflection `r ↦ n+1−r` fixes `H_n`. -/
lemma boundary_inv_sum_symm (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (((n + 1 - r : ℕ) : ℝ)⁻¹)) = cycleH1 n := by
  unfold cycleH1
  refine Finset.sum_nbij' (fun r => n + 1 - r) (fun r => n + 1 - r) ?_ ?_ ?_ ?_ ?_
  · intro r hr; rw [Finset.mem_Icc] at hr; show n + 1 - r ∈ Finset.Icc 1 n
    rw [Finset.mem_Icc]; omega
  · intro r hr; rw [Finset.mem_Icc] at hr; show n + 1 - r ∈ Finset.Icc 1 n
    rw [Finset.mem_Icc]; omega
  · intro r hr; rw [Finset.mem_Icc] at hr; show n + 1 - (n + 1 - r) = r; omega
  · intro r hr; rw [Finset.mem_Icc] at hr; show n + 1 - (n + 1 - r) = r; omega
  · intro r _; rfl

/-- Antidiagonal reciprocal sum `∑ 1/(r(n+1−r)) = 2 H_n/(n+1)`. -/
lemma boundary_pair_sum_eq_two_mul_harmonic_div (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹))
      = 2 * cycleH1 n / ((n + 1 : ℕ) : ℝ) := by
  have hstep :
      (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹))
        = (∑ r ∈ Finset.Icc 1 n,
            (((r : ℝ)⁻¹) + (((n + 1 - r : ℕ) : ℝ)⁻¹))) / ((n + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro r hr
    rw [inv_boundary_point hr]
  rw [hstep, Finset.sum_add_distrib, boundary_inv_sum_symm]
  unfold cycleH1
  ring

/-- **The exact pair-sum identity** `cycleFitPairSum n = H_n² − H_n^{(2)}`. -/
theorem cycleFitPairSum_eq_harmonic_sq_sub_harmonic2 (n : ℕ) :
    cycleFitPairSum n = cycleH1 n ^ 2 - cycleH2 n := by
  induction n with
  | zero => simp [cycleFitPairSum, cycleH1, cycleH2]
  | succ n ih =>
      rw [cycleFitPairSum_succ, ih, boundary_pair_sum_eq_two_mul_harmonic_div,
        cycleH1_succ, cycleH2_succ]
      have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch9 AnalyticCombinatorics.Ch9.LimitLaws AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS
open Filter Asymptotics
open scoped BigOperators Topology
theorem solution (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) -
      (FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ))) ^ 2
      = cycleH1 n - cycleH2 n := by
  rw [totalCycleCount_variance_eq_harmonic_add_fitPairSum_sub_sq,
    cycleFitPairSum_eq_harmonic_sq_sub_harmonic2]
  have hH : (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹) = cycleH1 n := rfl
  rw [hH]; ring
