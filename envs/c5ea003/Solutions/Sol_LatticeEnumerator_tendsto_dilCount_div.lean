-- Prove2me | solution 1 for LatticeEnumerator.tendsto_dilCount_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:09:06.966984+00:00
-- url     : https://prove2.me/submissions/c33e0a05-0b95-458b-aa7c-09fe7b785fc0

-- Sol generated from Cryptography/LatticePointEnumerator.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Theorems.Thm_LatticeEnumerator_approxSet_subset_closedBall
import Theorems.Thm_LatticeEnumerator_dilLattice_finite
import Theorems.Thm_LatticeEnumerator_eventually_mem_approxSet_iff
import Theorems.Thm_LatticeEnumerator_measurableSet_approxSet
import Theorems.Thm_LatticeEnumerator_measurableSet_cube
import Theorems.Thm_LatticeEnumerator_mem_cube
import Theorems.Thm_LatticeEnumerator_mem_dilLattice
import Theorems.Thm_LatticeEnumerator_volume_cube

/-!
# Lattice-point enumerators: asymptotics and rigidity

This file formalises the analytic core of the theory of *lattice-point enumerators*
`L_P(t) = |tP ∩ ℤ^d|` (`t > 0` a **real** dilation parameter) for bounded sets
`P ⊆ ℝ^d`, in the setting of the paper *A Fourier-analytic uniqueness theorem for
lattice-point enumerators*.

## Main definitions

* `LatticeEnumerator.shiftLattice P t y` : the set `{k ∈ ℤ^d : k/t - y ∈ P}` of lattice
  points of the dilated translate `t·(P + y)`.
* `LatticeEnumerator.dilLattice P t` : the lattice points `tP ∩ ℤ^d` (the case `y = 0`).
* `LatticeEnumerator.dilCount P t` : the lattice-point enumerator `L_P(t) = |tP ∩ ℤ^d|`.
* `LatticeEnumerator.shiftCount P t y` : the translated enumerator `|t(P + y) ∩ ℤ^d|`.
* `LatticeEnumerator.cube t k`, `LatticeEnumerator.floorMap t`,
  `LatticeEnumerator.approxSet P t` : the half-open `1/t`-cube attached to a lattice point,
  the coordinatewise rounding map `x ↦ ⌊t x⌋ / t`, and the union of the cubes attached to
  the counted lattice points.

## Main results

* `LatticeEnumerator.volume_approxSet` : the *exact* geometric identity
  `vol(A_t) = L_P(t) · t^{-d}`, where `A_t = {x : ⌊tx⌋/t ∈ P}` is a union of `L_P(t)`
  pairwise disjoint cubes of side `1/t`.
* `LatticeEnumerator.tendsto_dilCount_div` : the Gauss–Weyl counting theorem
  `L_P(t)/t^d → vol(P)` as `t → ∞`, for every bounded set with null topological frontier
  (Jordan measurable set).  The proof combines the exact identity above with dominated
  convergence, the domination coming from the fact that all the sets `A_t`, `t ≥ 1`, live
  in one fixed ball.
* `LatticeEnumerator.volume_eq_of_dilCount_eq` : two bounded Jordan measurable sets with
  the same real-parameter enumerator have the same volume.
* `LatticeEnumerator.volume_eq_of_dilCount_eq_convex` : the same statement for convex
  bodies, where Jordan measurability is automatic.
* `LatticeEnumerator.eq_of_shiftCount_eq` : a rigidity theorem.  If the enumerators of
  **all real translates** of two bounded sets agree, the sets are *equal* (not merely equal
  almost everywhere).  This isolates exactly where the difficulty of the integer-translate
  theorem lies: with real translates the periodisation is faithful at small `t`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

open LatticeEnumerator

variable {d : ℕ}

/-! ## Definitions -/










/-! ## Finiteness of the counted lattice sets -/




/-! ## The cube decomposition -/




/-- Distinct lattice points give disjoint cubes. -/
lemma pairwiseDisjoint_cube {t : ℝ} (ht : 0 < t) (S : Set (Fin d → ℤ)) :
    S.PairwiseDisjoint (cube t) := by
  intro k _ l _ hkl
  apply Set.disjoint_left.2
  intro x hx hx'
  exact hkl (funext fun i => ((mem_cube ht).1 hx i).symm.trans ((mem_cube ht).1 hx' i))

/-- `A_t` is the union of the cubes attached to the counted lattice points. -/
lemma approxSet_eq_iUnion (P : Set (Fin d → ℝ)) {t : ℝ} (ht : 0 < t) :
    approxSet P t = ⋃ k ∈ dilLattice P t, cube t k := by
  ext x
  simp only [approxSet, Set.mem_setOf_eq, Set.mem_iUnion, mem_dilLattice, exists_prop]
  constructor
  · intro hx
    exact ⟨fun i => ⌊t * x i⌋, hx, (mem_cube ht).2 fun i => rfl⟩
  · rintro ⟨k, hk, hxk⟩
    have hfl : floorMap t x = fun i => (k i : ℝ) / t := by
      funext i; simp [floorMap, (mem_cube ht).1 hxk i]
    rw [hfl]; exact hk


/-- **Exact geometric identity**: the volume of `A_t` is `L_P(t)` times the volume `t^{-d}`
of a single cube. -/
lemma volume_approxSet {P : Set (Fin d → ℝ)} (hP : Bornology.IsBounded P) {t : ℝ} (ht : 0 < t) :
    volume (approxSet P t) = dilCount P t • (ENNReal.ofReal (1 / t)) ^ d := by
  have hfin := dilLattice_finite hP ht
  have hU : approxSet P t = ⋃ k ∈ hfin.toFinset, cube t k := by
    rw [approxSet_eq_iUnion P ht]; simp [hfin.mem_toFinset]
  rw [hU, measure_biUnion_finset
      (pairwiseDisjoint_cube ht (↑hfin.toFinset : Set (Fin d → ℤ)))
      (fun k _ => measurableSet_cube t k),
    Finset.sum_congr rfl (fun k _ => volume_cube ht k), Finset.sum_const, dilCount,
    Set.ncard_eq_toFinset_card _ hfin]

/-- The real-valued form of the identity: `vol(A_t) = L_P(t)/t^d`. -/
lemma toReal_volume_approxSet {P : Set (Fin d → ℝ)} (hP : Bornology.IsBounded P) {t : ℝ}
    (ht : 0 < t) : (volume (approxSet P t)).toReal = (dilCount P t : ℝ) / t ^ d := by
  rw [volume_approxSet hP ht, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast, div_pow, one_pow]
  ring

/-! ## The rounding map and pointwise convergence -/




/-! ## The Gauss–Weyl counting theorem -/




/-! ## Rigidity for real translates -/




open LatticeEnumerator in
theorem solution{P : Set (Fin d → ℝ)} (hb : Bornology.IsBounded P)
    (hm : NullMeasurableSet P volume) (hfr : volume (frontier P) = 0) :
    Tendsto (fun t : ℝ => (dilCount P t : ℝ) / t ^ d) atTop (𝓝 (volume P).toReal) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hb
  set bound : (Fin d → ℝ) → ℝ :=
    (closedBall (0 : Fin d → ℝ) (R + 1)).indicator (fun _ => (1 : ℝ)) with hbound
  have hintP : ∫ x, P.indicator (fun _ => (1 : ℝ)) x = (volume P).toReal := by
    obtain ⟨u, hu, hsu⟩ := hm
    rw [integral_congr_ae (indicator_ae_eq_of_ae_eq_set hsu), integral_indicator_const _ hu,
      measure_congr hsu]
    simp [measureReal_def]
  have key : Tendsto (fun t : ℝ => ∫ x, (approxSet P t).indicator (fun _ => (1 : ℝ)) x) atTop
      (𝓝 ((volume P).toReal)) := by
    rw [← hintP]
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact (measurable_const.indicator (measurableSet_approxSet hb ht)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      filter_upwards with x
      have hsub := approxSet_subset_closedBall hR ht
      by_cases hx : x ∈ approxSet P t
      · rw [Set.indicator_of_mem hx, hbound, Set.indicator_of_mem (hsub hx)]
        simp
      · rw [Set.indicator_of_notMem hx]
        simp only [norm_zero, hbound]
        exact Set.indicator_nonneg (by intro _ _; norm_num) x
    · rw [hbound, integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const measure_closedBall_lt_top.ne
    · have hae : ∀ᵐ x : (Fin d → ℝ), x ∉ frontier P :=
        measure_eq_zero_iff_ae_notMem.1 hfr
      filter_upwards [hae] with x hx
      have hev := eventually_mem_approxSet_iff (P := P) hx
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev] with t ht
      by_cases hxP : x ∈ P
      · rw [Set.indicator_of_mem hxP, Set.indicator_of_mem (ht.2 hxP)]
      · rw [Set.indicator_of_notMem hxP, Set.indicator_of_notMem (fun h => hxP (ht.1 h))]
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [integral_indicator_const _ (measurableSet_approxSet hb ht), measureReal_def, smul_eq_mul,
    mul_one, toReal_volume_approxSet hb ht]
