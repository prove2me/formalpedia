-- Prove2me | solution 1 for MarkovChainCLT.exists_isSmallSet_measure_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-06T18:05:13.570559+00:00
-- url     : https://prove2.me/submissions/d6250e74-cc07-4fee-9521-d37f90f9c56e

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovDriftMinorization
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A geometrically ergodic chain has a small set of positive invariant measure

`exists_isSmallSet_measure_pos` (attempt **B**).

Route (deliberately different in its *machinery* from the "five-step Tonelli" plan):

* the exceptional sets are cut out **directly from the kernel Radon-Nikodym derivative**
  `Kernel.rnDeriv (iterKernel P n) (Kernel.const X π)`, which is *jointly* measurable, so
  the measurability of `x ↦ π {y | f n x y < 1/2}` comes from
  `measurable_measure_prodMk_left` and **the platform theorem
  `measurable_tvDist_kernel` is never used** — `tvDist` appears only inside the
  hypothesis, never inside a set we have to prove measurable;
* the whole estimate is carried in `ℝ≥0∞` (`lintegral`, `Measure.prod_apply` /
  `Measure.prod_apply_symm`), so no Bochner integral and no `toReal` bookkeeping;
* the Fubini swap is performed **on a single measurable subset of `X × X`** via
  `Measure.prod_apply` = `Measure.prod_apply_symm`, rather than on an iterated integral
  of indicator functions.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology ProbabilityTheory

set_option linter.unusedSectionVars false

namespace SmallSetB

open MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

/-! ### Step 0: the linchpin -/

/-- **The linchpin.** If `π A ≤ μ A + u` for every measurable `A`, then the
Radon-Nikodym density of `μ` w.r.t. `π` is `≥ 1/2` outside a set of `π`-measure `≤ 2u`. -/
theorem measure_rnDeriv_lt_half_le
    (μ π : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    [μ.HaveLebesgueDecomposition π] (u : ℝ≥0∞)
    (hu : ∀ A : Set X, MeasurableSet A → π A ≤ μ A + u) :
    π {y | μ.rnDeriv π y < 1/2} ≤ 2 * u := by
  classical
  set f := μ.rnDeriv π with hf
  set B : Set X := {y | f y < 1/2} with hB
  have hBm : MeasurableSet B := measurableSet_lt (Measure.measurable_rnDeriv μ π) measurable_const
  set hs := Measure.mutuallySingular_singularPart μ π
  set N : Set X := hs.nullSet with hN
  have hNm : MeasurableSet N := hs.measurableSet_nullSet
  have hsN : (μ.singularPart π) N = 0 := hs.measure_nullSet
  have hpiN : π Nᶜ = 0 := hs.measure_compl_nullSet
  have hpiB : π (B ∩ N) = π B := by
    refine le_antisymm (measure_mono Set.inter_subset_left) ?_
    have : π B ≤ π (B ∩ N) + π (B \ N) := measure_le_inter_add_diff π B N
    have hdiff : π (B \ N) = 0 :=
      measure_mono_null (Set.diff_subset_compl B N) hpiN
    simpa [hdiff] using this
  have hdecomp : π.withDensity f + μ.singularPart π = μ :=
    Measure.rnDeriv_add_singularPart μ π
  have hmuBN : μ (B ∩ N) ≤ (1/2) * π (B ∩ N) := by
    have h1 : μ (B ∩ N) = (π.withDensity f) (B ∩ N) + (μ.singularPart π) (B ∩ N) := by
      have := congrArg (fun m : Measure X => m (B ∩ N)) hdecomp
      simpa using this.symm
    have h2 : (μ.singularPart π) (B ∩ N) = 0 :=
      measure_mono_null Set.inter_subset_right hsN
    have h3 : (π.withDensity f) (B ∩ N) = ∫⁻ y in B ∩ N, f y ∂π :=
      withDensity_apply f (hBm.inter hNm)
    have h4 : ∫⁻ y in B ∩ N, f y ∂π ≤ ∫⁻ _ in B ∩ N, (1/2 : ℝ≥0∞) ∂π := by
      refine setLIntegral_mono_ae (by fun_prop) ?_
      filter_upwards with y hy
      exact le_of_lt hy.1
    rw [h1, h2, h3, add_zero]
    refine h4.trans ?_
    simp
  have hkey : π B ≤ (1/2) * π B + u := by
    calc π B = π (B ∩ N) := hpiB.symm
    _ ≤ μ (B ∩ N) + u := hu _ (hBm.inter hNm)
    _ ≤ (1/2) * π (B ∩ N) + u := by gcongr
    _ = (1/2) * π B + u := by rw [hpiB]
  have hfin : π B ≠ ⊤ := measure_ne_top π B
  have hhalf : (1/2 : ℝ≥0∞) * π B ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hfin
  have hle : π B - (1/2) * π B ≤ u :=
    tsub_le_iff_right.mpr (by rw [add_comm]; exact hkey)
  have hadd : (1/2 : ℝ≥0∞) * π B + (1/2) * π B = π B := by
    rw [← add_mul]; norm_num [ENNReal.inv_two_add_inv_two]
  have hsplit : π B - (1/2) * π B = (1/2) * π B :=
    ENNReal.sub_eq_of_eq_add hhalf hadd.symm
  rw [hsplit] at hle
  calc π B = 2 * ((1/2 : ℝ≥0∞) * π B) := by rw [two_mul]; exact hadd.symm
  _ ≤ 2 * u := by gcongr

/-! ### Step 1: reading the total-variation hypothesis -/

/-- Every `|μ A - ν A|` is dominated by `tvDist μ ν`: the defining set is bounded by `1`. -/
lemma abs_sub_le_tvDist (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set X} (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ tvDist μ ν := by
  refine le_csSup ⟨1, ?_⟩ ⟨A, hA, rfl⟩
  rintro r ⟨B, hB, rfl⟩
  have h1 : (μ B).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one : μ B ≤ 1)
  have h2 : (ν B).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one : ν B ≤ 1)
  have h3 : (0:ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  have h4 : (0:ℝ) ≤ (ν B).toReal := ENNReal.toReal_nonneg
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The one-sided consequence used downstream: `ν A ≤ μ A + ofReal c`. -/
lemma le_add_ofReal_of_tvDist_le (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ} (hc : 0 ≤ c) (h : tvDist μ ν ≤ c)
    (A : Set X) (hA : MeasurableSet A) :
    ν A ≤ μ A + ENNReal.ofReal c := by
  have hb := (abs_sub_le_tvDist μ ν hA).trans h
  rw [abs_sub_le_iff] at hb
  have hstep : (ν A).toReal ≤ (μ A).toReal + c := by linarith [hb.2]
  calc ν A = ENNReal.ofReal ((ν A).toReal) := (ENNReal.ofReal_toReal (measure_ne_top ν A)).symm
  _ ≤ ENNReal.ofReal ((μ A).toReal + c) := ENNReal.ofReal_le_ofReal hstep
  _ = ENNReal.ofReal ((μ A).toReal) + ENNReal.ofReal c :=
        ENNReal.ofReal_add ENNReal.toReal_nonneg hc
  _ = μ A + ENNReal.ofReal c := by rw [ENNReal.ofReal_toReal (measure_ne_top μ A)]

/-! ### Step 2: iterates compose -/

lemma iterKernel_add (P : Kernel X X) (m n : ℕ) :
    iterKernel P (m + n) = iterKernel P m ∘ₖ iterKernel P n := by
  induction m with
  | zero => simp [Kernel.id_comp]
  | succ m ih =>
      have : m + 1 + n = (m + n) + 1 := by omega
      rw [this, iterKernel_succ, ih, iterKernel_succ, Kernel.comp_assoc]

end SmallSetB

namespace SmallSetB
open MarkovChainCLT

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]

section Main

variable (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]

/-- The jointly measurable density of `Pⁿ(x,·)` w.r.t. `π`. -/
noncomputable def dens (n : ℕ) : X → X → ℝ≥0∞ :=
  Kernel.rnDeriv (iterKernel P n) (Kernel.const X π)

/-- The "bad" product set at lag `n`: where the density drops below `1/2`. -/
def badSet (n : ℕ) : Set (X × X) := {p : X × X | dens P π n p.1 p.2 < 1/2}

lemma measurableSet_badSet (n : ℕ) : MeasurableSet (badSet P π n) :=
  measurableSet_lt (Kernel.measurable_rnDeriv _ _) measurable_const

/-- `bad n x = π {y | dens n x y < 1/2}`. -/
noncomputable def bad (n : ℕ) (x : X) : ℝ≥0∞ := π (Prod.mk x ⁻¹' badSet P π n)

lemma measurable_bad (n : ℕ) : Measurable (bad P π n) :=
  measurable_measure_prodMk_left (measurableSet_badSet P π n)

lemma bad_eq (n : ℕ) (x : X) : bad P π n x = π {y | dens P π n x y < 1/2} := rfl

lemma measurable_dens (n : ℕ) (x : X) : Measurable (dens P π n x) :=
  Kernel.measurable_rnDeriv_right _ _ _

/-- The crux, transported to the kernel density. -/
lemma bad_le_of_tvDist_le (n : ℕ) (x : X) {c : ℝ} (hc : 0 ≤ c)
    (h : tvDist ((iterKernel P n) x) π ≤ c) :
    bad P π n x ≤ ENNReal.ofReal (2 * c) := by
  have hbd : ∀ A : Set X, MeasurableSet A →
      π A ≤ ((iterKernel P n) x) A + ENNReal.ofReal c :=
    le_add_ofReal_of_tvDist_le _ _ hc h
  have hcrux := measure_rnDeriv_lt_half_le ((iterKernel P n) x) π (ENNReal.ofReal c) hbd
  have hae : dens P π n x =ᵐ[π] ((iterKernel P n) x).rnDeriv π := by
    have := Kernel.rnDeriv_eq_rnDeriv_measure (κ := iterKernel P n)
      (η := Kernel.const X π) (a := x)
    simpa [dens, Kernel.const_apply] using this
  have hset : bad P π n x = π {y | ((iterKernel P n) x).rnDeriv π y < 1/2} := by
    rw [bad_eq]
    refine measure_congr ?_
    filter_upwards [hae] with y hy
    exact congrArg (fun v : ℝ≥0∞ => v < 1/2) hy
  rw [hset]
  refine hcrux.trans ?_
  rw [ENNReal.ofReal_mul (by norm_num)]
  norm_num

end Main

end SmallSetB

namespace SmallSetB
open MarkovChainCLT

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
variable (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]

/-- The density integrates back into the kernel: `∫_A f_n(z,·) dπ ≤ Pⁿ(z, A)`. -/
lemma setLIntegral_dens_le (n : ℕ) (z : X) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ y in A, dens P π n z y ∂π ≤ (iterKernel P n) z A := by
  have h := Kernel.setLIntegral_rnDeriv_le (κ := iterKernel P n) (η := Kernel.const X π)
    (a := z) hA
  rwa [Kernel.const_apply] at h

/-- Off the bad section the density is `≥ 1/2`, so `Pⁿ(z,·)` minorizes half of `π`
outside that section. -/
lemma half_measure_diff_le (n : ℕ) (z : X) {A : Set X} (hA : MeasurableSet A) :
    (1/2 : ℝ≥0∞) * π (A \ (Prod.mk z ⁻¹' badSet P π n)) ≤ (iterKernel P n) z A := by
  have hBm : MeasurableSet (Prod.mk z ⁻¹' badSet P π n) :=
    (measurableSet_badSet P π n).preimage measurable_prodMk_left
  calc (1/2 : ℝ≥0∞) * π (A \ (Prod.mk z ⁻¹' badSet P π n))
      = ∫⁻ _ in (A \ (Prod.mk z ⁻¹' badSet P π n)), (1/2 : ℝ≥0∞) ∂π := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ y in (A \ (Prod.mk z ⁻¹' badSet P π n)), dens P π n z y ∂π := by
        refine setLIntegral_mono (Kernel.measurable_rnDeriv_right _ _ _) ?_
        intro y hy
        have := hy.2
        simp only [Set.mem_preimage, badSet, Set.mem_setOf_eq, not_lt] at this
        exact this
    _ ≤ ∫⁻ y in A, dens P π n z y ∂π :=
        lintegral_mono' (Measure.restrict_mono Set.diff_subset le_rfl) le_rfl
    _ ≤ (iterKernel P n) z A := setLIntegral_dens_le P π n z hA

/-- `π.withDensity (f n x) ≤ Pⁿ(x, ·)`. -/
lemma withDensity_dens_le (n : ℕ) (x : X) :
    π.withDensity (dens P π n x) ≤ (iterKernel P n) x := by
  have h := Kernel.withDensity_rnDeriv_le (iterKernel P n) (Kernel.const X π) x
  rwa [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _) x, Kernel.const_apply] at h

end SmallSetB

namespace SmallSetB
open MarkovChainCLT

/-- `4 · (1/8) = 1/2` in `ℝ≥0∞` (numerals with `⁻¹` are not `norm_num`-transparent here). -/
lemma four_mul_eighth : (4:ℝ≥0∞) * (1/8) = 1/2 := by
  have h : (8:ℝ≥0∞)⁻¹ = 4⁻¹ * 2⁻¹ := by
    rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]; norm_num
  simp only [one_div, h, ← mul_assoc]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Numeric identity used to collect the four constants at the end. -/
lemma const_collect : (1/2 : ℝ≥0∞) * ((1/2 : ℝ≥0∞) * ((1/2 : ℝ≥0∞) * 8)) = 1 := by
  simp only [one_div]
  have h1 : (2:ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]; norm_num
  have h2 : (4:ℝ≥0∞)⁻¹ * 2⁻¹ = 8⁻¹ := by
    rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]; norm_num
  calc (2:ℝ≥0∞)⁻¹ * (2⁻¹ * (2⁻¹ * 8)) = ((2:ℝ≥0∞)⁻¹ * 2⁻¹ * 2⁻¹) * 8 := by ring
  _ = 8⁻¹ * 8 := by rw [h1, h2]
  _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]

theorem exists_isSmallSet_measure_pos
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ C : Set X, MeasurableSet C ∧ IsSmallSet P C ∧ 0 < π C := by
  classical
  obtain ⟨M, t, hM0, ht0, ht1, hrate⟩ := hgeo
  -- ## Step 1: measurable level sets of the density defect, exhausting `X`
  set S : ℕ → Set X := fun K =>
    {x | ∀ m : ℕ, 1 ≤ m → bad P π m x ≤ ENNReal.ofReal (2 * ((K:ℝ) * t ^ m))} with hSdef
  have hSm : ∀ K : ℕ, MeasurableSet (S K) := by
    intro K
    have hrw : S K =
        ⋂ m : ℕ, {x | 1 ≤ m → bad P π m x ≤ ENNReal.ofReal (2 * ((K:ℝ) * t ^ m))} := by
      ext x; simp [hSdef]
    rw [hrw]
    refine MeasurableSet.iInter fun m => ?_
    by_cases hm : 1 ≤ m
    · have he : {x : X | 1 ≤ m → bad P π m x ≤ ENNReal.ofReal (2 * ((K:ℝ) * t ^ m))}
          = {x : X | bad P π m x ≤ ENNReal.ofReal (2 * ((K:ℝ) * t ^ m))} := by
        ext x; simp [hm]
      rw [he]
      exact measurableSet_le (measurable_bad P π m) measurable_const
    · have he : {x : X | 1 ≤ m → bad P π m x ≤ ENNReal.ofReal (2 * ((K:ℝ) * t ^ m))}
          = (Set.univ : Set X) := by
        ext x; simp [hm]
      rw [he]; exact MeasurableSet.univ
  have hcover : (⋃ K : ℕ, S K) = (Set.univ : Set X) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨K, hK⟩ := exists_nat_ge (M x)
    refine ⟨K, fun m hm => ?_⟩
    have h1 : bad P π m x ≤ ENNReal.ofReal (2 * (M x * t ^ m)) :=
      bad_le_of_tvDist_le P π m x (mul_nonneg (hM0 x) (pow_nonneg ht0 m)) (hrate x m hm)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : M x * t ^ m ≤ (K:ℝ) * t ^ m :=
      mul_le_mul_of_nonneg_right hK (pow_nonneg ht0 m)
    linarith
  obtain ⟨K, hKpos⟩ : ∃ K : ℕ, 0 < π (S K) := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ K : ℕ, π (S K) = 0 := fun K => le_antisymm (hcon K) zero_le
    have hnull := measure_iUnion_null (μ := π) hz
    rw [hcover, measure_univ] at hnull
    exact one_ne_zero hnull
  -- ## Step 2: the candidate set and its measure
  set C : Set X := S K with hCdef
  have hCm : MeasurableSet C := hSm K
  set σ : ℝ≥0∞ := π C with hσdef
  have hσpos : 0 < σ := hKpos
  have hσne : σ ≠ 0 := hσpos.ne'
  have hσtop : σ ≠ ⊤ := measure_ne_top π C
  have hσle : σ ≤ 1 := prob_le_one
  set w : ℝ≥0∞ := σ / 16 with hwdef
  have hw16 : 16 * w = σ := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
  have hwne : w ≠ 0 := by
    intro h; rw [h, mul_zero] at hw16; exact hσne hw16.symm
  have hwtop : w ≠ ⊤ := by
    rw [hwdef]; simp [ENNReal.div_eq_top, hσtop]
  have h4wne : (4 : ℝ≥0∞) * w ≠ 0 := by
    simp [hwne]
  have h4wtop : (4 : ℝ≥0∞) * w ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hwtop
  -- ## Step 3: choose the lag `n`
  set cR : ℝ := min ((4 * w).toReal) (1/8) with hcRdef
  have hcRpos : 0 < cR := lt_min (ENNReal.toReal_pos h4wne h4wtop) (by norm_num)
  obtain ⟨n, hn1, hnlt⟩ : ∃ n : ℕ, 1 ≤ n ∧ 2 * ((K:ℝ) * t ^ n) < cR := by
    have hlim : Tendsto (fun m : ℕ => 2 * ((K:ℝ) * t ^ m)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun m : ℕ => t ^ m) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1
      have h1 := (h0.const_mul ((K:ℝ))).const_mul (2:ℝ)
      simpa using h1
    have hev : ∀ᶠ m : ℕ in atTop, 2 * ((K:ℝ) * t ^ m) < cR :=
      hlim.eventually_lt_const hcRpos
    obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists
    exact ⟨N, hN.2, hN.1⟩
  set a : ℝ≥0∞ := ENNReal.ofReal (2 * ((K:ℝ) * t ^ n)) with hadef
  have ha4w : a ≤ 4 * w := by
    refine (ENNReal.ofReal_le_ofReal hnlt.le).trans ?_
    refine (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans ?_
    rw [ENNReal.ofReal_toReal h4wtop]
  have ha8 : a ≤ 1/8 := by
    refine (ENNReal.ofReal_le_ofReal hnlt.le).trans ?_
    refine (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans ?_
    simp
  have hCbad : ∀ x ∈ C, bad P π n x ≤ a := fun x hx => hx n hn1
  -- ## Step 4: the good target set `D`
  set V : Set (X × X) := (Prod.fst ⁻¹' C) ∩ badSet P π n with hVdef
  have hVm : MeasurableSet V :=
    (hCm.preimage measurable_fst).inter (measurableSet_badSet P π n)
  set g : X → ℝ≥0∞ := fun y => π ((fun z => (z, y)) ⁻¹' V) with hgdef
  have hgm : Measurable g := measurable_measure_prodMk_right hVm
  set D : Set X := {y | g y ≤ 4 * w} with hDdef
  have hDm : MeasurableSet D := measurableSet_le hgm measurable_const
  have hgint : ∫⁻ y, g y ∂π ≤ a * σ := by
    have e1 : ∫⁻ y, g y ∂π = (π.prod π) V := (Measure.prod_apply_symm hVm).symm
    have e2 : (π.prod π) V = ∫⁻ z, π (Prod.mk z ⁻¹' V) ∂π := Measure.prod_apply hVm
    have e3 : ∀ z : X, π (Prod.mk z ⁻¹' V) = C.indicator (fun z => bad P π n z) z := by
      intro z
      by_cases hz : z ∈ C
      · rw [Set.indicator_of_mem hz]
        congr 1
        ext y; simp [hVdef, hz]
      · rw [Set.indicator_of_notMem hz]
        have he : Prod.mk z ⁻¹' V = (∅ : Set X) := by ext y; simp [hVdef, hz]
        rw [he, measure_empty]
    rw [e1, e2]
    simp_rw [e3]
    rw [lintegral_indicator hCm]
    calc ∫⁻ z in C, bad P π n z ∂π ≤ ∫⁻ _ in C, a ∂π :=
          setLIntegral_mono measurable_const hCbad
    _ = a * σ := by rw [setLIntegral_const, hσdef]
  have hDc : π Dᶜ ≤ 1/2 := by
    have hmk : (4 * w) * π {y | 4 * w ≤ g y} ≤ ∫⁻ y, g y ∂π :=
      mul_meas_ge_le_lintegral₀ hgm.aemeasurable (4 * w)
    have hsub : Dᶜ ⊆ {y | 4 * w ≤ g y} := by
      intro y hy
      simp only [hDdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hy
      exact le_of_lt hy
    have h1 : (4 * w) * π Dᶜ ≤ ∫⁻ y, g y ∂π := by
      refine le_trans ?_ hmk
      gcongr
    have h3 : (4 * w) * π Dᶜ ≤ (4 * w) * (4 * a) := by
      refine h1.trans (hgint.trans ?_)
      rw [← hw16]
      exact le_of_eq (by ring)
    have h4 : π Dᶜ ≤ 4 * a := (ENNReal.mul_le_mul_iff_right h4wne h4wtop).mp h3
    refine h4.trans ?_
    calc (4:ℝ≥0∞) * a ≤ 4 * (1/8) := by gcongr
    _ = 1/2 := four_mul_eighth
  have hDhalf : (1/2 : ℝ≥0∞) ≤ π D := by
    have hsum : π D + π Dᶜ = 1 := by rw [measure_add_measure_compl hDm, measure_univ]
    have h2 : (1/2 : ℝ≥0∞) + 1/2 ≤ π D + 1/2 := by
      calc (1/2 : ℝ≥0∞) + 1/2 = 1 := ENNReal.add_halves 1
      _ = π D + π Dᶜ := hsum.symm
      _ ≤ π D + 1/2 := by gcongr
    exact (ENNReal.add_le_add_iff_right (by norm_num)).mp h2
  have hDne : π D ≠ 0 := by
    intro hh; rw [hh] at hDhalf; norm_num at hDhalf
  have hDtop : π D ≠ ⊤ := measure_ne_top π D
  -- ## Step 5: the minorizing probability measure
  set Q : Measure X := (π D)⁻¹ • π.restrict D with hQdef
  have hQprob : IsProbabilityMeasure Q := by
    constructor
    rw [hQdef]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    exact ENNReal.inv_mul_cancel hDne hDtop
  refine ⟨C, hCm, ⟨2 * n, by omega, w.toReal, ENNReal.toReal_pos hwne hwtop, Q, hQprob, ?_⟩,
    hσpos⟩
  intro x hx A hA
  rw [ENNReal.ofReal_toReal hwtop]
  -- ## Step 6: the two-step minorization
  set G : Set X := C \ (Prod.mk x ⁻¹' badSet P π n) with hGdef
  have hbadxm : MeasurableSet (Prod.mk x ⁻¹' badSet P π n) :=
    (measurableSet_badSet P π n).preimage measurable_prodMk_left
  have hGm : MeasurableSet G := hCm.diff hbadxm
  set E : Set X := A ∩ D with hEdef
  have hEm : MeasurableSet E := hA.inter hDm
  set V3 : Set (X × X) := (Prod.fst ⁻¹' G) ∩ (badSet P π n)ᶜ with hV3def
  have hV3m : MeasurableSet V3 :=
    (hGm.preimage measurable_fst).inter (measurableSet_badSet P π n).compl
  set V2 : Set (X × X) := V3 ∩ (Prod.snd ⁻¹' E) with hV2def
  have hV2m : MeasurableSet V2 := hV3m.inter (hEm.preimage measurable_snd)
  set r : X → ℝ≥0∞ := fun y => π ((fun z => (z, y)) ⁻¹' V3) with hrdef
  have hrm : Measurable r := measurable_measure_prodMk_right hV3m
  have hzsec : ∀ z : X, π (Prod.mk z ⁻¹' V2)
      = G.indicator (fun z => π (E \ (Prod.mk z ⁻¹' badSet P π n))) z := by
    intro z
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_mem hz]
      congr 1
      ext y
      simp [hV2def, hV3def, hz, Set.mem_diff, and_comm]
    · rw [Set.indicator_of_notMem hz]
      have he : Prod.mk z ⁻¹' V2 = (∅ : Set X) := by ext y; simp [hV2def, hV3def, hz]
      rw [he, measure_empty]
  have hysec : ∀ y : X, π ((fun z => (z, y)) ⁻¹' V2) = E.indicator r y := by
    intro y
    by_cases hy : y ∈ E
    · rw [Set.indicator_of_mem hy]
      congr 1
      ext z
      simp [hV2def, hV3def, hy]
    · rw [Set.indicator_of_notMem hy]
      have he : (fun z => (z, y)) ⁻¹' V2 = (∅ : Set X) := by ext z; simp [hV2def, hV3def, hy]
      rw [he, measure_empty]
  have hfub : ∫⁻ z in G, π (E \ (Prod.mk z ⁻¹' badSet P π n)) ∂π = ∫⁻ y in E, r y ∂π := by
    rw [← lintegral_indicator hGm, ← lintegral_indicator hEm]
    simp_rw [← hzsec, ← hysec]
    rw [← Measure.prod_apply hV2m, ← Measure.prod_apply_symm hV2m]
  have hrlow : ∀ y ∈ E, 8 * w ≤ r y := by
    intro y hy
    have hcov : C ⊆ ((fun z => (z, y)) ⁻¹' V3) ∪ ((Prod.mk x ⁻¹' badSet P π n) ∪
        ((fun z => (z, y)) ⁻¹' V)) := by
      intro z hz
      by_cases hz1 : z ∈ Prod.mk x ⁻¹' badSet P π n
      · exact Or.inr (Or.inl hz1)
      · by_cases hz2 : (z, y) ∈ badSet P π n
        · refine Or.inr (Or.inr ?_)
          simp only [Set.mem_preimage, hVdef, Set.mem_inter_iff]
          exact ⟨hz, hz2⟩
        · refine Or.inl ?_
          simp only [Set.mem_preimage, hV3def, hGdef, Set.mem_inter_iff, Set.mem_compl_iff,
            Set.mem_diff]
          exact ⟨⟨hz, hz1⟩, hz2⟩
    have hle : σ ≤ r y + (a + 4 * w) := by
      calc σ = π C := hσdef
      _ ≤ π (((fun z => (z, y)) ⁻¹' V3) ∪ ((Prod.mk x ⁻¹' badSet P π n) ∪
            ((fun z => (z, y)) ⁻¹' V))) := measure_mono hcov
      _ ≤ r y + π ((Prod.mk x ⁻¹' badSet P π n) ∪ ((fun z => (z, y)) ⁻¹' V)) :=
            measure_union_le _ _
      _ ≤ r y + (π (Prod.mk x ⁻¹' badSet P π n) + π ((fun z => (z, y)) ⁻¹' V)) := by
            gcongr
            exact measure_union_le _ _
      _ ≤ r y + (a + 4 * w) := by
            gcongr
            · exact hCbad x hx
            · exact hy.2
    have h8 : (8:ℝ≥0∞) * w + 8 * w ≤ r y + 8 * w := by
      calc (8:ℝ≥0∞) * w + 8 * w = 16 * w := by ring
      _ = σ := hw16
      _ ≤ r y + (a + 4 * w) := hle
      _ ≤ r y + (4 * w + 4 * w) := by gcongr
      _ = r y + 8 * w := by ring
    exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hwtop)).mp h8
  have hEint : (8 * w) * π E ≤ ∫⁻ y in E, r y ∂π := by
    calc (8 * w) * π E = ∫⁻ _ in E, (8 * w : ℝ≥0∞) ∂π := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in E, r y ∂π := setLIntegral_mono hrm hrlow
  have hkey : (1/2 : ℝ≥0∞) * ((1/2 : ℝ≥0∞) * ((8 * w) * π E)) ≤ (iterKernel P (2*n)) x A := by
    have hcomp : (iterKernel P (2*n)) x A
        = ∫⁻ z, (iterKernel P n) z A ∂((iterKernel P n) x) := by
      have h2n : 2 * n = n + n := by omega
      rw [h2n, iterKernel_add, Kernel.comp_apply' _ _ _ hA]
    rw [hcomp]
    have step1 : ∫⁻ z, (iterKernel P n) z A ∂(π.withDensity (dens P π n x))
        ≤ ∫⁻ z, (iterKernel P n) z A ∂((iterKernel P n) x) :=
      lintegral_mono' (withDensity_dens_le P π n x) le_rfl
    refine le_trans ?_ step1
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_dens P π n x)
      (Kernel.measurable_coe _ hA)]
    simp only [Pi.mul_apply]
    have step2 : ∫⁻ z in G, (1/2 : ℝ≥0∞) * ((1/2 : ℝ≥0∞) *
        π (E \ (Prod.mk z ⁻¹' badSet P π n))) ∂π
        ≤ ∫⁻ z, dens P π n x z * (iterKernel P n) z A ∂π := by
      refine le_trans (setLIntegral_mono ?_ ?_) (setLIntegral_le_lintegral _ _)
      · exact (measurable_dens P π n x).mul (Kernel.measurable_coe _ hA)
      · intro z hz
        have hd : (1/2 : ℝ≥0∞) ≤ dens P π n x z := by
          have hz2 := hz.2
          simp only [Set.mem_preimage, badSet, Set.mem_setOf_eq, not_lt] at hz2
          exact hz2
        have hEA : (iterKernel P n) z E ≤ (iterKernel P n) z A :=
          measure_mono (by rw [hEdef]; exact Set.inter_subset_left)
        exact mul_le_mul' hd ((half_measure_diff_le P π n z hEm).trans hEA)
    refine le_trans ?_ step2
    rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    gcongr
    rw [hfub]
    exact hEint
  have hQA : π D * Q A = π E := by
    rw [hQdef]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hDne hDtop, one_mul, hEdef]
  have hfinal : (1/2 : ℝ≥0∞) * Q A ≤ π E := by
    rw [← hQA]; gcongr
  have hcollect : (1/2 : ℝ≥0∞) * ((1/2 : ℝ≥0∞) * ((8 * w) * ((1/2 : ℝ≥0∞) * Q A)))
      = w * Q A := by
    calc (1/2 : ℝ≥0∞) * ((1/2 : ℝ≥0∞) * ((8 * w) * ((1/2 : ℝ≥0∞) * Q A)))
        = ((1/2 : ℝ≥0∞) * ((1/2 : ℝ≥0∞) * ((1/2 : ℝ≥0∞) * 8))) * (w * Q A) := by ring
    _ = 1 * (w * Q A) := by rw [const_collect]
    _ = w * Q A := one_mul _
  rw [← hcollect]
  refine le_trans ?_ hkey
  gcongr

end SmallSetB

/-! ## The submitted statement -/

open MarkovChainCLT in
/-- **A geometrically ergodic chain has a small set of positive invariant measure.** -/
theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ C : Set X, MeasurableSet C ∧ IsSmallSet P C ∧ 0 < π C :=
  SmallSetB.exists_isSmallSet_measure_pos P π hP hgeo

#print axioms solution
