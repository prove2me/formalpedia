-- Prove2me | solution 1 for AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete.rCycles_tendstoInDistribution_poisson
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:19:56.487067+00:00
-- url     : https://prove2.me/submissions/d51a31b7-7a8c-4175-a98e-b985569c7390

import Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesFactorialMoment
import Mathlib
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

namespace AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete end AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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

/-!
# Pointwise pmf convergence on `ℕ` implies weak convergence

This file supplies a reusable discrete bridge from pointwise convergence of
singleton masses on `ℕ` to Mathlib's weak convergence topology on
`ProbabilityMeasure ℕ`, and applies it to the fixed-point count in a uniform
random permutation.
-/

noncomputable section

open Filter
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace PMFToDistribution

open MeasureTheory

/-- On `ℕ`, convergence of all singleton masses implies weak convergence of
probability measures. This is the reusable discrete bridge used below.

The proof is the portmanteau finite-subset argument: finite sums of singleton
masses converge, finite unions are contained in the open set, and the limiting
measure of an arbitrary subset of `ℕ` is the supremum of its finite
approximations. -/
theorem probabilityMeasure_nat_tendsto_of_tendsto_singleton
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (h : ∀ j : ℕ,
      Tendsto (fun n : ℕ => (μs n : Measure ℕ) ({j} : Set ℕ)) atTop
        (𝓝 ((μ : Measure ℕ) ({j} : Set ℕ)))) :
    Tendsto μs atTop (𝓝 μ) := by
  classical
  refine MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat' ?_
  intro G _hG
  have hfinite_le :
      ∀ s : Finset ℕ, (∀ j ∈ s, j ∈ G) →
        (∑ j ∈ s, (μ : Measure ℕ) ({j} : Set ℕ)) ≤
          atTop.liminf (fun n : ℕ => (μs n : Measure ℕ) G) := by
    intro s hsG
    have hsum_tendsto :
        Tendsto
          (fun n : ℕ => ∑ j ∈ s, (μs n : Measure ℕ) ({j} : Set ℕ))
          atTop
          (𝓝 (∑ j ∈ s, (μ : Measure ℕ) ({j} : Set ℕ))) :=
      tendsto_finset_sum s (fun j _hj => h j)
    rw [← hsum_tendsto.liminf_eq]
    refine Filter.liminf_le_liminf (Eventually.of_forall ?_)
      (by isBoundedDefault)
      (by isBoundedDefault)
    intro n
    have hdisj : (s : Set ℕ).PairwiseDisjoint (fun j => ({j} : Set ℕ)) := by
      intro a _ha b _hb hne
      change Disjoint ({a} : Set ℕ) ({b} : Set ℕ)
      rw [Set.disjoint_singleton_left]
      simpa using hne
    calc
      (∑ j ∈ s, (μs n : Measure ℕ) ({j} : Set ℕ))
          = (μs n : Measure ℕ) (⋃ j ∈ s, ({j} : Set ℕ)) := by
              exact (MeasureTheory.measure_biUnion_finset hdisj
                (fun j _hj => measurableSet_singleton j)).symm
      _ ≤ (μs n : Measure ℕ) G := by
              refine measure_mono ?_
              intro x hx
              simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
              rcases hx with ⟨j, hj, hxj⟩
              subst hxj
              exact hsG x hj
  have hμG :
      (μ : Measure ℕ) G =
        ∑' j : ℕ, G.indicator (fun j => (μ : Measure ℕ) ({j} : Set ℕ)) j := by
    exact (Measure.tsum_indicator_apply_singleton (μ : Measure ℕ) G (by simp)).symm
  rw [hμG, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro s
  calc
    (∑ j ∈ s, G.indicator (fun j => (μ : Measure ℕ) ({j} : Set ℕ)) j)
        = ∑ j ∈ s.filter (fun j => j ∈ G), (μ : Measure ℕ) ({j} : Set ℕ) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            by_cases hjG : j ∈ G
            · simp [hjG]
            · simp [hjG]
    _ ≤ atTop.liminf (fun n : ℕ => (μs n : Measure ℕ) G) :=
            hfinite_le (s.filter (fun j => j ∈ G))
              (fun j hj => (Finset.mem_filter.mp hj).2)

/-- A real-valued pmf version of
`probabilityMeasure_nat_tendsto_of_tendsto_singleton`. -/
theorem probabilityMeasure_nat_tendsto_of_tendsto_pmfReal
    {p : ℕ → ℕ → ℝ} {q : ℕ → ℝ}
    {μs : ℕ → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (hp : ∀ n j, (μs n : Measure ℕ) ({j} : Set ℕ) = ENNReal.ofReal (p n j))
    (hq : ∀ j, (μ : Measure ℕ) ({j} : Set ℕ) = ENNReal.ofReal (q j))
    (hconv : ∀ j : ℕ, Tendsto (fun n : ℕ => p n j) atTop (𝓝 (q j))) :
    Tendsto μs atTop (𝓝 μ) :=
  probabilityMeasure_nat_tendsto_of_tendsto_singleton fun j => by
    simpa [hp, hq] using ENNReal.tendsto_ofReal (hconv j)

end PMFToDistribution
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

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

lemma rCycleCount_eq_cycleType_count_of_ne_one {n r : ℕ}
    (hr : r ≠ 1) (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ = σ.cycleType.count r := by
  simp [rCycleCount, hr]

lemma expPartial_tendsto_exp (x : ℝ) :
    Tendsto (fun m : ℕ => expPartial x m) atTop (𝓝 (Real.exp x)) := by
  simpa [expPartial, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x).tendsto_sum_nat

lemma nat_div_sub_tendsto_atTop {r : ℕ} (hr : 0 < r) (j : ℕ) :
    Tendsto (fun n : ℕ => n / r - j) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨(b + j) * r, fun n hn => ?_⟩
  have hdiv : b + j ≤ n / r := (Nat.le_div_iff_mul_le hr).2 hn
  exact Nat.le_sub_of_add_le hdiv

lemma nat_div_sub_add_one_tendsto_atTop {r : ℕ} (hr : 0 < r) (j : ℕ) :
    Tendsto (fun n : ℕ => n / r - j + 1) atTop atTop :=
  (tendsto_add_atTop_nat 1).comp (nat_div_sub_tendsto_atTop hr j)

theorem rCyclePMFFormula_tendsto_poisson {r : ℕ} (hr : 0 < r) (j : ℕ) :
    Tendsto (fun n : ℕ => rCyclePMFFormula n r j) atTop
      (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) j)) := by
  have hidx : Tendsto (fun n : ℕ => n / r - j + 1) atTop atTop :=
    nat_div_sub_add_one_tendsto_atTop hr j
  have hpartial :
      Tendsto
        (fun n : ℕ => expPartial (-(r : ℝ)⁻¹) (n / r - j + 1))
        atTop (𝓝 (Real.exp (-(r : ℝ)⁻¹))) :=
    (expPartial_tendsto_exp (-(r : ℝ)⁻¹)).comp hidx
  have hmain :
      Tendsto
        (fun n : ℕ =>
          (((r : ℝ) ^ j * j.factorial)⁻¹) *
            expPartial (-(r : ℝ)⁻¹) (n / r - j + 1))
        atTop
        (𝓝 ((((r : ℝ) ^ j * j.factorial)⁻¹) *
          Real.exp (-(r : ℝ)⁻¹))) :=
    tendsto_const_nhds.mul hpartial
  have heq :
      (fun n : ℕ => rCyclePMFFormula n r j) =ᶠ[atTop]
        fun n : ℕ =>
          (((r : ℝ) ^ j * j.factorial)⁻¹) *
            expPartial (-(r : ℝ)⁻¹) (n / r - j + 1) := by
    filter_upwards [eventually_ge_atTop (r * j)] with n hn
    simp [rCyclePMFFormula, Nat.ne_of_gt hr, hn]
  refine Tendsto.congr' heq.symm ?_
  convert hmain using 1
  rw [ProbabilityTheory.poissonPMFReal]
  simp [poissonRate]
  have hrℝ : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hrℝ, pow_ne_zero j hrℝ, hjfac]

theorem rCyclePMF_tendsto_poisson_of_eventually_formula {r : ℕ} (hr : 0 < r)
    (hformula : ∀ j : ℕ,
      (fun n : ℕ => rCyclePMF n r j) =ᶠ[atTop]
        fun n : ℕ => rCyclePMFFormula n r j) :
    ∀ j : ℕ,
      Tendsto (fun n : ℕ => rCyclePMF n r j) atTop
        (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) j)) := by
  intro j
  exact Tendsto.congr' (hformula j).symm (rCyclePMFFormula_tendsto_poisson hr j)

lemma rCycle_law_singleton (n r j : ℕ) :
    (Measure.map (rCycleCount n r) (uniformPermMeasure n)) ({j} : Set ℕ) =
      ENNReal.ofReal (rCyclePMF n r j) := by
  classical
  have hpre :
      (rCycleCount n r) ⁻¹' ({j} : Set ℕ) =
        {σ : Equiv.Perm (Fin n) | rCycleCount n r σ = j} := by
    ext σ
    simp
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton j), hpre]
  unfold uniformPermMeasure
  rw [PMF.toMeasure_uniformOfFintype_apply]
  · rw [Fintype.card_perm, Fintype.card_fin]
    change (Fintype.card {σ : Equiv.Perm (Fin n) //
        rCycleCount n r σ = j} : ℝ≥0∞) / (n.factorial : ℝ≥0∞) =
      ENNReal.ofReal (rCyclePMF n r j)
    unfold rCyclePMF rCycleFavourableCount
    rw [ENNReal.ofReal_div_of_pos]
    · congr
      · exact_mod_cast rfl
      · exact_mod_cast rfl
    · positivity
  · simp

lemma poisson_law_singleton (r : ℝ≥0) (j : ℕ) :
    (ProbabilityTheory.poissonMeasure r) ({j} : Set ℕ) =
      ENNReal.ofReal (ProbabilityTheory.poissonPMFReal r j) := by
  rw [ProbabilityTheory.poissonMeasure]
  exact PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)

/-- Pointwise pmf convergence implies weak convergence of the laws of `r`-cycle
counts.  The nontrivial combinatorial input is the supplied pmf limit. -/
theorem rCycle_law_tendsto_poisson_of_tendsto_pmf
    {r : ℕ}
    (hpmf : ∀ j : ℕ,
      Tendsto (fun n : ℕ => rCyclePMF n r j) atTop
        (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) j))) :
    Tendsto (fun n : ℕ => rCycleLaw n r) atTop
      (𝓝 (poissonProbabilityMeasure (poissonRate r))) := by
  refine PMFToDistribution.probabilityMeasure_nat_tendsto_of_tendsto_pmfReal
    (p := fun n j => rCyclePMF n r j)
    (q := fun j => ProbabilityTheory.poissonPMFReal (poissonRate r) j) ?_ ?_ ?_
  · intro n j
    exact rCycle_law_singleton n r j
  · intro j
    exact poisson_law_singleton (poissonRate r) j
  · intro j
    exact hpmf j

/-- Full convergence in distribution from pointwise pmf convergence. -/
theorem rCycles_tendstoInDistribution_poisson_of_tendsto_pmf
    {r : ℕ}
    (hpmf : ∀ j : ℕ,
      Tendsto (fun n : ℕ => rCyclePMF n r j) atTop
        (𝓝 (ProbabilityTheory.poissonPMFReal (poissonRate r) j))) :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => rCycleCount n r ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (poissonRate r)) where
  forall_aemeasurable n := rCycleCount_aemeasurable n r
  aemeasurable_limit := by exact measurable_id.aemeasurable
  tendsto := by
    simpa [rCycleLaw, poissonProbabilityMeasure] using
      rCycle_law_tendsto_poisson_of_tendsto_pmf (r := r) hpmf

theorem rCycles_tendstoInDistribution_poisson_of_eventually_formula {r : ℕ} (hr : 0 < r)
    (hformula : ∀ j : ℕ,
      (fun n : ℕ => rCyclePMF n r j) =ᶠ[atTop]
        fun n : ℕ => rCyclePMFFormula n r j) :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => rCycleCount n r ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (poissonRate r)) :=
  rCycles_tendstoInDistribution_poisson_of_tendsto_pmf
    (rCyclePMF_tendsto_poisson_of_eventually_formula hr hformula)

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

lemma card_subtype_eq_sum_indicator {α : Type*} [Fintype α]
    (X : α → ℕ) (j : ℕ) :
    (Fintype.card {a : α // X a = j} : ℝ) =
      ∑ a : α, if X a = j then (1 : ℝ) else 0 := by
  rw [Fintype.card_subtype]
  rw [Finset.sum_boole]

lemma finite_pmf_eq_factorial_moment_sum {α : Type*} [Fintype α]
    (X : α → ℕ) {M j : ℕ} (hX : ∀ a : α, X a ≤ M) :
    (Fintype.card {a : α // X a = j} : ℝ) / (Fintype.card α : ℝ) =
      ∑ i ∈ Finset.range (M - j + 1),
        (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
          ((∑ a : α, ((X a).descFactorial (j + i) : ℝ)) / (Fintype.card α : ℝ)) := by
  have hpoint :
      ∀ a : α,
        (if X a = j then (1 : ℝ) else 0) =
          ∑ i ∈ Finset.range (M - j + 1),
            ((-1 : ℝ) ^ i) *
              (((X a).descFactorial (j + i) : ℝ) /
                (i.factorial * (j.factorial : ℝ))) := by
    intro a
    exact (factorial_kernel_sum_eq_indicator (M := M) (x := X a) (j := j) (hX a)).symm
  calc
    (Fintype.card {a : α // X a = j} : ℝ) / (Fintype.card α : ℝ)
        = (∑ a : α, if X a = j then (1 : ℝ) else 0) /
            (Fintype.card α : ℝ) := by
          rw [card_subtype_eq_sum_indicator X j]
    _ = (∑ a : α, ∑ i ∈ Finset.range (M - j + 1),
            ((-1 : ℝ) ^ i) *
              (((X a).descFactorial (j + i) : ℝ) /
                (i.factorial * (j.factorial : ℝ)))) /
          (Fintype.card α : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact hpoint a
    _ = (∑ i ∈ Finset.range (M - j + 1), ∑ a : α,
            ((-1 : ℝ) ^ i) *
              (((X a).descFactorial (j + i) : ℝ) /
                (i.factorial * (j.factorial : ℝ)))) /
          (Fintype.card α : ℝ) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (M - j + 1),
        (∑ a : α,
            ((-1 : ℝ) ^ i) *
              (((X a).descFactorial (j + i) : ℝ) /
                (i.factorial * (j.factorial : ℝ)))) /
          (Fintype.card α : ℝ) := by
          rw [Finset.sum_div]
    _ = ∑ i ∈ Finset.range (M - j + 1),
        (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
          ((∑ a : α, ((X a).descFactorial (j + i) : ℝ)) / (Fintype.card α : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          calc
            (∑ a : α,
                ((-1 : ℝ) ^ i) *
                  (((X a).descFactorial (j + i) : ℝ) /
                    (i.factorial * (j.factorial : ℝ)))) /
                (Fintype.card α : ℝ)
                =
                (((( -1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
                  (∑ a : α, ((X a).descFactorial (j + i) : ℝ))) /
                (Fintype.card α : ℝ) := by
                  congr 1
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro a _ha
                  ring
            _ = (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
                  ((∑ a : α, ((X a).descFactorial (j + i) : ℝ)) /
                    (Fintype.card α : ℝ)) := by
                  ring

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

lemma factorial_moment_sum_eq_formula_sum {n r j : ℕ} (hr : 0 < r) :
    (∑ i ∈ Finset.range (n / r - j + 1),
        (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
          ((r : ℝ) ^ (-(j + i : ℤ)))) =
      (((r : ℝ) ^ j * (j.factorial : ℝ))⁻¹) *
        expPartial (-(r : ℝ)⁻¹) (n / r - j + 1) := by
  rw [expPartial]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact factorial_moment_term_eq_expPartial_term r j i hr

theorem rCyclePMF_eq_formula {r : ℕ} (hr : 0 < r) :
    ∀ j n : ℕ, rCyclePMF n r j = rCyclePMFFormula n r j := by
  intro j n
  by_cases hjn : r * j ≤ n
  · have hjM : j ≤ n / r := by
      exact (Nat.le_div_iff_mul_le hr).2 (by simpa [Nat.mul_comm] using hjn)
    have hinv := finite_pmf_eq_factorial_moment_sum
      (α := Equiv.Perm (Fin n))
      (X := fun σ : Equiv.Perm (Fin n) => rCycleCount n r σ)
      (M := n / r) (j := j)
      (fun σ => rCycleCount_le_div (n := n) (r := r) hr σ)
    have hpmf_sum :
        rCyclePMF n r j =
          ∑ i ∈ Finset.range (n / r - j + 1),
            (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
              ((∑ σ : Equiv.Perm (Fin n),
                  ((rCycleCount n r σ).descFactorial (j + i) : ℝ)) /
                (n.factorial : ℝ)) := by
      unfold rCyclePMF rCycleFavourableCount
      simpa [Fintype.card_perm, Fintype.card_fin] using hinv
    have hmoment :
        ∀ i ∈ Finset.range (n / r - j + 1),
          ((∑ σ : Equiv.Perm (Fin n),
              ((rCycleCount n r σ).descFactorial (j + i) : ℝ)) /
            (n.factorial : ℝ)) =
              (r : ℝ) ^ (-(j + i : ℤ)) := by
      intro i hi
      have hi_le : i ≤ n / r - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hik : j + i ≤ n / r := by omega
      have hmul' : (j + i) * r ≤ n := (Nat.le_div_iff_mul_le hr).1 hik
      have hmul : r * (j + i) ≤ n := by simpa [Nat.mul_comm] using hmul'
      simpa [FixedPointsPoissonNS.uniformPermExpectation] using
        factorialMoment_rCycle (n := n) (r := r) (k := j + i) hr hmul
    calc
      rCyclePMF n r j
          = ∑ i ∈ Finset.range (n / r - j + 1),
              (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
                ((∑ σ : Equiv.Perm (Fin n),
                    ((rCycleCount n r σ).descFactorial (j + i) : ℝ)) /
                  (n.factorial : ℝ)) := hpmf_sum
      _ = ∑ i ∈ Finset.range (n / r - j + 1),
              (((-1 : ℝ) ^ i) / (i.factorial * (j.factorial : ℝ))) *
                ((r : ℝ) ^ (-(j + i : ℤ))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmoment i hi]
      _ = (((r : ℝ) ^ j * (j.factorial : ℝ))⁻¹) *
            expPartial (-(r : ℝ)⁻¹) (n / r - j + 1) :=
            factorial_moment_sum_eq_formula_sum (n := n) (r := r) (j := j) hr
      _ = rCyclePMFFormula n r j := by
            simp [rCyclePMFFormula, Nat.ne_of_gt hr, hjn]
  · have hjgt : n / r < j := by
      have hnot : ¬ j * r ≤ n := by
        simpa [Nat.mul_comm] using hjn
      exact Nat.lt_of_not_ge (fun hjM => hnot ((Nat.le_div_iff_mul_le hr).1 hjM))
    have hempty :
        IsEmpty {σ : Equiv.Perm (Fin n) // rCycleCount n r σ = j} := by
      rw [isEmpty_subtype]
      intro σ hσ
      have hle := rCycleCount_le_div (n := n) (r := r) hr σ
      omega
    have hfav : rCycleFavourableCount n r j = 0 := by
      unfold rCycleFavourableCount
      haveI := hempty
      exact Fintype.card_eq_zero
    simp [rCyclePMF, rCyclePMFFormula, hfav, Nat.ne_of_gt hr, hjn]

theorem rCyclePMF_eventually_eq_formula {r : ℕ} (hr : 0 < r) :
    ∀ j : ℕ,
      (fun n : ℕ => rCyclePMF n r j) =ᶠ[atTop]
        fun n : ℕ => rCyclePMFFormula n r j := by
  intro j
  exact Filter.Eventually.of_forall fun n => rCyclePMF_eq_formula (r := r) hr j n

end Complete
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch9 AnalyticCombinatorics.Ch9.LimitLaws AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Complete
open Filter MeasureTheory
open scoped Topology ENNReal NNReal
theorem solution {r : ℕ} (hr : 0 < r) :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n (ω : Equiv.Perm (Fin n)) => rCycleCount n r ω)
      atTop
      (fun x : ℕ => x)
      uniformPermMeasure
      (ProbabilityTheory.poissonMeasure (poissonRate r)) :=
  rCycles_tendstoInDistribution_poisson_of_eventually_formula
    hr (rCyclePMF_eventually_eq_formula hr)
