-- Prove2me | solution 1 for Hirsch.cubic_circuit_walk_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-08T20:09:33.885626+00:00
-- url     : https://prove2.me/submissions/2307b4b4-3b84-4f25-bece-897c71800386

import Definitions.Def_Hirsch_circuit_model
import Definitions.Def_Hirsch_circuit_slack_model
import Mathlib


set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

theorem circuitRowSupport_eq_support_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) :
    circuitRowSupport a g = Function.support (rowMap a g) := by
  ext i
  rfl

theorem slack_nonneg_iff_mem_Hpoly {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    (∀ i, 0 ≤ slack a b x i) ↔ x ∈ Hpoly a b := by
  constructor
  · intro h i
    have hi := h i
    dsimp [slack] at hi
    linarith
  · intro h i
    have hi := h i
    dsimp [slack]
    linarith

theorem slack_mem_SlackPoly_iff {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slack a b x ∈ SlackPoly a b ↔ x ∈ Hpoly a b := by
  constructor
  · intro h
    exact (slack_nonneg_iff_mem_Hpoly a b x).mp h.2
  · intro hx
    refine ⟨⟨x, rfl⟩, ?_⟩
    exact (slack_nonneg_iff_mem_Hpoly a b x).mpr hx

theorem slack_sub_slack_eq_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    slack a b x - slack a b y = rowMap a (y - x) := by
  funext i
  simp only [Pi.sub_apply, slack, rowMap, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_right]
  ring

theorem slack_line {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    slack a b (x + t • (y - x)) =
      slack a b x + t • (slack a b y - slack a b x) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, slack,
    inner_add_right, inner_smul_right, inner_sub_right]
  ring

theorem slack_injective_of_rowMap_injective {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a)) :
    Function.Injective (slack a b) := by
  intro x y hxy
  apply hinj
  funext i
  have hi := congrFun hxy i
  simp only [slack] at hi
  change ⟪a i, x⟫ = ⟪a i, y⟫
  linarith

theorem isRowCircuit_iff_elementary_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (rowMap a))
    (g : EuclideanSpace ℝ (Fin d)) :
    IsRowCircuit a g ↔
      IsElementaryIn (LinearMap.range (rowMap a)) (rowMap a g) := by
  constructor
  · rintro ⟨hg0, hmin⟩
    refine ⟨?_, ⟨g, rfl⟩, ?_⟩
    · intro hz
      apply hg0
      apply hinj
      simpa using hz
    · intro w hw0 hwRange hsub
      rcases hwRange with ⟨h, rfl⟩
      have hh0 : h ≠ 0 := by
        intro hh
        subst h
        simp at hw0
      have hsub' : circuitRowSupport a h ⊆ circuitRowSupport a g := by
        simpa [circuitRowSupport_eq_support_rowMap] using hsub
      have hout := hmin h hh0 hsub'
      simpa [circuitRowSupport_eq_support_rowMap] using hout
  · rintro ⟨hmap0, _hRange, hmin⟩
    refine ⟨?_, ?_⟩
    · intro hg0
      subst g
      exact hmap0 (by simp)
    · intro h hh0 hsub
      have hmh0 : rowMap a h ≠ 0 := by
        intro hz
        apply hh0
        apply hinj
        simpa using hz
      have hsub' : Function.support (rowMap a h) ⊆
          Function.support (rowMap a g) := by
        simpa [circuitRowSupport_eq_support_rowMap] using hsub
      have hout := hmin (rowMap a h) hmh0 ⟨h, rfl⟩ hsub'
      simpa [circuitRowSupport_eq_support_rowMap] using hout

theorem rowCircuitStep_iff_slackCircuitStep {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (x y : EuclideanSpace ℝ (Fin d)) :
    RowCircuitStep a b x y ↔
      SlackCircuitStep a b (slack a b x) (slack a b y) := by
  constructor
  · rintro ⟨hx, hy, hcirc, hmax⟩
    refine ⟨(slack_mem_SlackPoly_iff a b x).mpr hx,
      (slack_mem_SlackPoly_iff a b y).mpr hy, ?_, ?_⟩
    · rw [slack_sub_slack_eq_rowMap]
      exact (isRowCircuit_iff_elementary_rowMap a hinj (y - x)).mp hcirc
    · intro t ht hmem
      have hline := slack_line a b x y t
      rw [← hline] at hmem
      exact hmax t ht ((slack_mem_SlackPoly_iff a b _).mp hmem)
  · rintro ⟨hx, hy, hcirc, hmax⟩
    refine ⟨(slack_mem_SlackPoly_iff a b x).mp hx,
      (slack_mem_SlackPoly_iff a b y).mp hy, ?_, ?_⟩
    · rw [slack_sub_slack_eq_rowMap] at hcirc
      exact (isRowCircuit_iff_elementary_rowMap a hinj (y - x)).mpr hcirc
    · intro t ht hfeas
      apply hmax t ht
      have hmem := (slack_mem_SlackPoly_iff a b _).mpr hfeas
      rw [slack_line a b x y t] at hmem
      exact hmem

theorem rowCircuitWalk_to_slackCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    RowCircuitWalk a b L u v →
      SlackCircuitWalk a b L (slack a b u) (slack a b v) := by
  rintro ⟨w, hw0, hwL, hfeas, hstep⟩
  refine ⟨fun j => slack a b (w j), ?_, ?_, ?_, ?_⟩
  · simpa [hw0]
  · simpa [hwL]
  · intro j hj
    exact (slack_mem_SlackPoly_iff a b (w j)).mpr (hfeas j hj)
  · intro j hj
    rcases hstep j hj with hstay | hmove
    · left
      simpa [hstay]
    · right
      exact (rowCircuitStep_iff_slackCircuitStep a b hinj (w j) (w (j + 1))).mp hmove


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Natura's conformal partial order: common closed orthant and bounded magnitudes. -/
def ConformalTo {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ x i * y i ∧ |x i| ≤ |y i|
notation:50 x " ⊑ᶜ " y => ConformalTo x y

theorem conformalTo_refl {n : ℕ} (x : Fin n → ℝ) : x ⊑ᶜ x := by
  intro i
  exact ⟨mul_self_nonneg _, le_rfl⟩

theorem conformalTo_zero {n : ℕ} (x : Fin n → ℝ) :
    (0 : Fin n → ℝ) ⊑ᶜ x := by
  intro i
  simp

theorem conformalTo_support_subset {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) : Function.support x ⊆ Function.support y := by
  intro i hix
  simp only [Function.mem_support] at hix ⊢
  intro hy0
  have habs := (hxy i).2
  rw [hy0, abs_zero] at habs
  exact hix (abs_eq_zero.mp (le_antisymm habs (abs_nonneg _)))

theorem conformalTo_eq_zero_of_right_eq_zero {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) {i : Fin n} (hy : y i = 0) : x i = 0 := by
  have habs := (hxy i).2
  rw [hy, abs_zero] at habs
  exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))

theorem conformalTo_smul {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) {c : ℝ} (_hc : 0 ≤ c) :
    (c • x) ⊑ᶜ (c • y) := by
  intro i
  constructor
  · simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith [(hxy i).1, sq_nonneg c]
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hxy i).2 (abs_nonneg c)

theorem conformalTo_coord_nonneg_of_right_nonneg {n : ℕ}
    {x y : Fin n → ℝ} (hxy : x ⊑ᶜ y) {i : Fin n} (hy : 0 ≤ y i) :
    0 ≤ x i := by
  rcases lt_or_eq_of_le hy with hypos | hy0
  · have hsign := (hxy i).1
    nlinarith
  · rw [conformalTo_eq_zero_of_right_eq_zero hxy hy0.symm]

theorem conformalTo_coord_nonpos_of_right_nonpos {n : ℕ}
    {x y : Fin n → ℝ} (hxy : x ⊑ᶜ y) {i : Fin n} (hy : y i ≤ 0) :
    x i ≤ 0 := by
  rcases lt_or_eq_of_le hy with hyneg | hy0
  · have hsign := (hxy i).1
    nlinarith
  · rw [conformalTo_eq_zero_of_right_eq_zero hxy hy0]

/-- Subtracting a conformal piece preserves the orthant and magnitude bound. -/
theorem conformalTo_sub_right {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) : (y - x) ⊑ᶜ y := by
  intro i
  rcases le_total 0 (y i) with hy | hy
  · have hx0 := conformalTo_coord_nonneg_of_right_nonneg hxy hy
    have habs := (hxy i).2
    rw [abs_of_nonneg hx0, abs_of_nonneg hy] at habs
    have hres0 : 0 ≤ y i - x i := by linarith
    constructor
    · exact mul_nonneg hres0 hy
    · change |y i - x i| ≤ |y i|
      rw [abs_of_nonneg hres0, abs_of_nonneg hy]
      linarith
  · have hx0 := conformalTo_coord_nonpos_of_right_nonpos hxy hy
    have habs := (hxy i).2
    rw [abs_of_nonpos hx0, abs_of_nonpos hy] at habs
    have hres0 : y i - x i ≤ 0 := by linarith
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos hres0 hy
    · change |y i - x i| ≤ |y i|
      rw [abs_of_nonpos hres0, abs_of_nonpos hy]
      linarith

theorem abs_add_residual_eq_abs {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) (i : Fin n) :
    |x i| + |y i - x i| = |y i| := by
  rcases le_total 0 (y i) with hy | hy
  · have hx0 := conformalTo_coord_nonneg_of_right_nonneg hxy hy
    have habs := (hxy i).2
    rw [abs_of_nonneg hx0, abs_of_nonneg hy] at habs
    have hres0 : 0 ≤ y i - x i := by linarith
    rw [abs_of_nonneg hx0, abs_of_nonneg hres0, abs_of_nonneg hy]
    ring
  · have hx0 := conformalTo_coord_nonpos_of_right_nonpos hxy hy
    have habs := (hxy i).2
    rw [abs_of_nonpos hx0, abs_of_nonpos hy] at habs
    have hres0 : y i - x i ≤ 0 := by linarith
    rw [abs_of_nonpos hx0, abs_of_nonpos hres0, abs_of_nonpos hy]
    ring

/-- Weighted absolute-value potential; zero weights omit coordinates. -/
noncomputable def weightedL1 {n : ℕ} (w x : Fin n → ℝ) : ℝ :=
  ∑ i, w i * |x i|

theorem weightedL1_conformal_split {n : ℕ} (w : Fin n → ℝ)
    {x y : Fin n → ℝ} (hxy : x ⊑ᶜ y) :
    weightedL1 w y = weightedL1 w x + weightedL1 w (y - x) := by
  simp only [weightedL1, ← Finset.sum_add_distrib, Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_add, abs_add_residual_eq_abs hxy i]

theorem support_smul_eq {n : ℕ} (z : Fin n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    Function.support (c • z) = Function.support z := by
  ext i
  simp [Function.mem_support, hc]

theorem isElementaryIn_smul {n : ℕ} (K : Submodule ℝ (Fin n → ℝ))
    {z : Fin n → ℝ} (hz : IsElementaryIn K z) {c : ℝ} (hc : c ≠ 0) :
    IsElementaryIn K (c • z) := by
  rcases hz with ⟨hz0, hzK, hmin⟩
  refine ⟨?_, K.smul_mem c hzK, ?_⟩
  · intro hcz
    apply hz0
    have := congrArg (fun q : Fin n → ℝ => c⁻¹ • q) hcz
    simpa [hc] using this
  · intro q hq0 hqK hqsub
    rw [support_smul_eq z hc] at hqsub ⊢
    exact hmin q hq0 hqK hqsub

end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace HirschCircuit

/-- Finite support of a coordinate vector. -/
noncomputable def supportFinset {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

@[simp] theorem mem_supportFinset {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    i ∈ supportFinset x ↔ x i ≠ 0 := by
  simp [supportFinset]

/-- A half-scaled perturbation stays conformal when the perturbation is no
larger coordinatewise than the original conformal vector. -/
theorem half_perturb_conformal {n : ℕ} {w z h : Fin n → ℝ} {t : ℝ}
    (hwz : ConformalTo w z)
    (hsub : Function.support h ⊆ Function.support w)
    (hpert : ∀ i, |t * h i| ≤ |w i|) :
    ConformalTo ((1 / 2 : ℝ) • (w + t • h)) z := by
  intro i
  have habsw := (hwz i).2
  have hp := hpert i
  have hadd : |w i + t * h i| ≤ |w i| + |t * h i| := abs_add_le _ _
  have hyabs : |((1 / 2 : ℝ) * (w i + t * h i))| ≤ |w i| := by
    rw [abs_mul]
    norm_num
    nlinarith [hadd]
  constructor
  · rcases lt_trichotomy (w i) 0 with hwneg | hwzero | hwpos
    · have hznonpos : z i ≤ 0 := by
        have hs := (hwz i).1
        nlinarith
      have hupper : t * h i ≤ -w i := by
        have hself := le_abs_self (t * h i)
        rw [abs_of_neg hwneg] at hp
        linarith
      have hy : (1 / 2 : ℝ) * (w i + t * h i) ≤ 0 := by linarith
      exact mul_nonneg_of_nonpos_of_nonpos hy hznonpos
    · have hhzero : h i = 0 := by
        by_contra hh
        have hm : i ∈ Function.support h := by simpa [Function.mem_support] using hh
        have := hsub hm
        simpa [Function.mem_support, hwzero] using this
      simp [hwzero, hhzero]
    · have hznonneg : 0 ≤ z i := by
        have hs := (hwz i).1
        nlinarith
      have hlower : -w i ≤ t * h i := by
        have hself := neg_abs_le (t * h i)
        rw [abs_of_pos hwpos] at hp
        linarith
      have hy : 0 ≤ (1 / 2 : ℝ) * (w i + t * h i) := by linarith
      exact mul_nonneg hy hznonneg
  · simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hyabs.trans habsw

/-- Every nonzero vector in a finite-dimensional subspace admits a
support-minimal elementary vector conformal to it. This is the circuit piece
existence lemma underlying conformal circuit decompositions. -/
theorem exists_elementary_conformal {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) {z : Fin n → ℝ}
    (hzK : z ∈ K) (hz0 : z ≠ 0) :
    ∃ g : Fin n → ℝ, IsElementaryIn K g ∧ ConformalTo g z := by
  classical
  let Good : (Fin n → ℝ) → Prop := fun w =>
    w ≠ 0 ∧ w ∈ K ∧ ConformalTo w z
  have hzGood : Good z := ⟨hz0, hzK, conformalTo_refl z⟩
  have hex : ∃ k : ℕ, ∃ w : Fin n → ℝ,
      (supportFinset w).card = k ∧ Good w :=
    ⟨(supportFinset z).card, z, rfl, hzGood⟩
  obtain ⟨w, hwcard, hwGood⟩ := Nat.find_spec hex
  have hmin : ∀ y : Fin n → ℝ, Good y →
      (supportFinset w).card ≤ (supportFinset y).card := by
    intro y hy
    rw [hwcard]
    exact Nat.find_min' hex ⟨y, rfl, hy⟩
  refine ⟨w, ?_, hwGood.2.2⟩
  refine ⟨hwGood.1, hwGood.2.1, ?_⟩
  intro h hh0 hhK hsub
  by_contra hnrev
  obtain ⟨k, hwk, hhk⟩ := Set.not_subset.mp hnrev
  have hwk0 : w k ≠ 0 := by simpa [Function.mem_support] using hwk
  have hhk0 : h k = 0 := by simpa [Function.mem_support] using hhk

  let D : Finset (Fin n) := Finset.univ.filter (fun i => h i ≠ 0)
  have hexh : ∃ i, h i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hh0
    funext i
    exact hall i
  have hD : D.Nonempty := by
    obtain ⟨i, hi⟩ := hexh
    exact ⟨i, by simp [D, hi]⟩
  obtain ⟨q, hqD, hratio⟩ :=
    D.exists_min_image (fun i => |w i| / |h i|) hD
  have hhq0 : h q ≠ 0 := (Finset.mem_filter.mp hqD).2
  have hwq0 : w q ≠ 0 := by
    have hqSuppH : q ∈ Function.support h := by
      simpa [Function.mem_support] using hhq0
    have := hsub hqSuppH
    simpa [Function.mem_support] using this
  let t : ℝ := -(w q / h q)
  have hcancel : w q + t * h q = 0 := by
    dsimp [t]
    field_simp [hhq0]
    ring
  have hpert : ∀ i, |t * h i| ≤ |w i| := by
    intro i
    by_cases hhi0 : h i = 0
    · simp [hhi0]
    · have hiD : i ∈ D := by simp [D, hhi0]
      have hle := hratio i hiD
      have hmul := mul_le_mul_of_nonneg_right hle (abs_nonneg (h i))
      have habshi : |h i| ≠ 0 := abs_ne_zero.mpr hhi0
      calc
        |t * h i| = (|w q| / |h q|) * |h i| := by
          simp [t, abs_mul, abs_div]
        _ ≤ (|w i| / |h i|) * |h i| := hmul
        _ = |w i| := by field_simp [habshi]
  let y : Fin n → ℝ := (1 / 2 : ℝ) • (w + t • h)
  have hyConf : ConformalTo y z := by
    exact half_perturb_conformal hwGood.2.2 hsub hpert
  have hyK : y ∈ K := by
    exact K.smul_mem _ (K.add_mem hwGood.2.1 (K.smul_mem t hhK))
  have hy0 : y ≠ 0 := by
    intro hy
    have hyk := congrFun hy k
    simp only [y, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hhk0, mul_zero, add_zero] at hyk
    norm_num at hyk
    exact hwk0 hyk
  have hySub : supportFinset y ⊆ supportFinset w := by
    intro i hi
    simp only [mem_supportFinset] at hi ⊢
    intro hwi0
    have hhi0 : h i = 0 := by
      by_contra hh
      have hm : i ∈ Function.support h := by simpa [Function.mem_support] using hh
      have := hsub hm
      simpa [Function.mem_support, hwi0] using this
    apply hi
    simp [y, hwi0, hhi0]
  have hqIn : q ∈ supportFinset w := by simp [hwq0]
  have hqOut : q ∉ supportFinset y := by
    simp only [mem_supportFinset, not_not]
    change (1 / 2 : ℝ) * (w q + t * h q) = 0
    rw [hcancel]
    ring
  have hyNe : supportFinset y ≠ supportFinset w := by
    intro heq
    have : q ∈ supportFinset y := heq.symm ▸ hqIn
    exact hqOut this
  have hstrict : supportFinset y ⊂ supportFinset w :=
    ssubset_of_ne_of_subset hyNe hySub
  have hcardlt : (supportFinset y).card < (supportFinset w).card :=
    Finset.card_lt_card hstrict
  have hcardmin := hmin y ⟨hy0, hyK, hyConf⟩
  omega

/-- Rescale an elementary conformal direction until at least one coordinate of
the residual vanishes. The scaled vector is still elementary and conformal,
and subtracting it strictly decreases support. -/
theorem exists_saturating_elementary_conformal {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) {z : Fin n → ℝ}
    (hzK : z ∈ K) (hz0 : z ≠ 0) :
    ∃ g : Fin n → ℝ,
      IsElementaryIn K g ∧ ConformalTo g z ∧
      ConformalTo (z - g) z ∧
      (supportFinset (z - g)).card < (supportFinset z).card := by
  classical
  obtain ⟨g0, hg0elem, hg0conf⟩ := exists_elementary_conformal K hzK hz0
  have hg00 : g0 ≠ 0 := hg0elem.1
  have hD : (supportFinset g0).Nonempty := by
    by_contra hnone
    have hzero : supportFinset g0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    apply hg00
    funext i
    by_contra hi
    have : i ∈ supportFinset g0 := by simpa using hi
    simpa [hzero] using this
  obtain ⟨q, hqD, hmin⟩ :=
    (supportFinset g0).exists_min_image (fun i => |z i| / |g0 i|) hD
  have hgq0 : g0 q ≠ 0 := by simpa using hqD
  have hzq0 : z q ≠ 0 := by
    have hsub := conformalTo_support_subset hg0conf
    have hqSupp : q ∈ Function.support g0 := by simpa [Function.mem_support] using hgq0
    have := hsub hqSupp
    simpa [Function.mem_support] using this
  let c : ℝ := |z q| / |g0 q|
  have hcpos : 0 < c := div_pos (abs_pos.mpr hzq0) (abs_pos.mpr hgq0)
  have hc0 : 0 ≤ c := le_of_lt hcpos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have habs : ∀ i, |c * g0 i| ≤ |z i| := by
    intro i
    by_cases hgi0 : g0 i = 0
    · simp [hgi0]
    · have hiD : i ∈ supportFinset g0 := by simpa using hgi0
      have hle := hmin i hiD
      have hmul := mul_le_mul_of_nonneg_right hle (abs_nonneg (g0 i))
      have habsgi : |g0 i| ≠ 0 := abs_ne_zero.mpr hgi0
      calc
        |c * g0 i| = c * |g0 i| := by rw [abs_mul, abs_of_nonneg hc0]
        _ ≤ (|z i| / |g0 i|) * |g0 i| := by simpa [c] using hmul
        _ = |z i| := by field_simp [habsgi]
  let g : Fin n → ℝ := c • g0
  have hgconf : ConformalTo g z := by
    intro i
    constructor
    · simp only [g, Pi.smul_apply, smul_eq_mul]
      have hs := (hg0conf i).1
      nlinarith
    · simpa only [g, Pi.smul_apply, smul_eq_mul] using habs i
  have hgelem : IsElementaryIn K g := by
    exact isElementaryIn_smul K hg0elem hcne
  have hresconf : ConformalTo (z - g) z := conformalTo_sub_right hgconf
  have hcancel : g q = z q := by
    change c * g0 q = z q
    dsimp [c]
    rcases lt_or_gt_of_ne hzq0 with hzneg | hzpos
    · have hgqle : g0 q ≤ 0 :=
        conformalTo_coord_nonpos_of_right_nonpos hg0conf (le_of_lt hzneg)
      have hgqneg : g0 q < 0 := lt_of_le_of_ne hgqle hgq0
      rw [abs_of_neg hzneg, abs_of_neg hgqneg]
      field_simp [hgq0]
    · have hgqge : 0 ≤ g0 q :=
        conformalTo_coord_nonneg_of_right_nonneg hg0conf (le_of_lt hzpos)
      have hgqpos : 0 < g0 q := lt_of_le_of_ne hgqge (Ne.symm hgq0)
      rw [abs_of_pos hzpos, abs_of_pos hgqpos]
      field_simp [hgq0]
  have hsub : supportFinset (z - g) ⊆ supportFinset z := by
    intro i hi
    simp only [mem_supportFinset] at hi ⊢
    intro hzi
    have hzres := conformalTo_eq_zero_of_right_eq_zero hresconf hzi
    exact hi hzres
  have hqIn : q ∈ supportFinset z := by simpa using hzq0
  have hqOut : q ∉ supportFinset (z - g) := by
    simp only [mem_supportFinset, not_not, Pi.sub_apply]
    rw [hcancel, sub_self]
  have hne : supportFinset (z - g) ≠ supportFinset z := by
    intro heq
    exact hqOut (heq.symm ▸ hqIn)
  have hstrict : supportFinset (z - g) ⊂ supportFinset z :=
    ssubset_of_ne_of_subset hne hsub
  exact ⟨g, hgelem, hgconf, hresconf, Finset.card_lt_card hstrict⟩


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

/-- Conformality is transitive. -/
theorem conformalTo_trans {n : ℕ} {x y z : Fin n → ℝ}
    (hxy : ConformalTo x y) (hyz : ConformalTo y z) :
    ConformalTo x z := by
  intro i
  constructor
  · rcases le_total 0 (z i) with hz | hz
    · have hy0 := conformalTo_coord_nonneg_of_right_nonneg hyz hz
      have hx0 := conformalTo_coord_nonneg_of_right_nonneg hxy hy0
      exact mul_nonneg hx0 hz
    · have hy0 := conformalTo_coord_nonpos_of_right_nonpos hyz hz
      have hx0 := conformalTo_coord_nonpos_of_right_nonpos hxy hy0
      exact mul_nonneg_of_nonpos_of_nonpos hx0 hz
  · exact (hxy i).2.trans (hyz i).2

/-- Any vector in a finite-dimensional subspace is an exact sum of elementary
vectors conformal to it, using no more pieces than its support cardinality. -/
theorem exists_elementary_conformal_decomposition {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (z : Fin n → ℝ) (hzK : z ∈ K) :
    ∃ gs : List (Fin n → ℝ),
      gs.length ≤ (supportFinset z).card ∧
      (∀ g ∈ gs, IsElementaryIn K g ∧ ConformalTo g z) ∧
      gs.sum = z := by
  classical
  have aux : ∀ k : ℕ, ∀ z : Fin n → ℝ,
      z ∈ K → (supportFinset z).card = k →
      ∃ gs : List (Fin n → ℝ),
        gs.length ≤ (supportFinset z).card ∧
        (∀ g ∈ gs, IsElementaryIn K g ∧ ConformalTo g z) ∧
        gs.sum = z := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro z hzK hk
      by_cases hz0 : z = 0
      · subst z
        refine ⟨[], by simp, ?_, by simp⟩
        simp
      · obtain ⟨g, hgelem, hgconf, hresconf, hcardlt⟩ :=
          exists_saturating_elementary_conformal K hzK hz0
        let r : Fin n → ℝ := z - g
        have hrK : r ∈ K := by
          exact K.sub_mem hzK hgelem.2.1
        have hrlt : (supportFinset r).card < k := by
          simpa [r, hk] using hcardlt
        obtain ⟨gs, hlen, hall, hsum⟩ :=
          ih (supportFinset r).card hrlt r hrK rfl
        refine ⟨g :: gs, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨hgelem, hgconf⟩
          · obtain ⟨hpelem, hpconf⟩ := hall p hp
            exact ⟨hpelem, conformalTo_trans hpconf hresconf⟩
        · rw [List.sum_cons, hsum]
          dsimp [r]
          funext i
          simp only [Pi.add_apply, Pi.sub_apply]
          ring
  exact aux (supportFinset z).card z hzK rfl

/-- The decomposition above uses at most the ambient number of coordinates. -/
theorem exists_elementary_conformal_decomposition_le_n {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (z : Fin n → ℝ) (hzK : z ∈ K) :
    ∃ gs : List (Fin n → ℝ),
      gs.length ≤ n ∧
      (∀ g ∈ gs, IsElementaryIn K g ∧ ConformalTo g z) ∧
      gs.sum = z := by
  obtain ⟨gs, hlen, hall, hsum⟩ :=
    exists_elementary_conformal_decomposition K z hzK
  refine ⟨gs, ?_, hall, hsum⟩
  have hcard : (supportFinset z).card ≤ n := by
    have hsub : supportFinset z ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.card_le_card hsub
    simpa using this
  exact hlen.trans hcard


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Delete redundant rows without changing the set. For separated endpoints,
the midpoint is strictly feasible for every retained row. This is the
normalization part of the circuit-routing child, independent of its bound. -/
theorem exists_irredundant_strict_model
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hv : v ∈ Hpoly a b)
    (hsep : ∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hpoly a b ∧
      RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) ∧
      StrictlyFeasibleRows (fun j => a (e j)) (fun j => b (e j)) := by
  classical
  let Good : Finset (Fin n) → Prop := fun S =>
    ∀ x : EuclideanSpace ℝ (Fin d),
      (∀ i ∈ S, ⟪a i, x⟫ ≤ b i) → x ∈ Hpoly a b
  have hall : Good Finset.univ := by
    intro x hx i
    exact hx i (Finset.mem_univ i)
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), S.card = k ∧ Good S :=
    ⟨n, Finset.univ, by simp, hall⟩
  obtain ⟨S, hScard, hGood⟩ := Nat.find_spec hex
  have hmin : ∀ T : Finset (Fin n), Good T → S.card ≤ T.card := by
    intro T hT
    rw [hScard]
    exact Nat.find_min' hex ⟨T, rfl, hT⟩
  have hessential : ∀ i ∈ S, ∃ x : EuclideanSpace ℝ (Fin d),
      (∀ j ∈ S, j ≠ i → ⟪a j, x⟫ ≤ b j) ∧ b i < ⟪a i, x⟫ := by
    intro i hi
    by_contra hn
    have hrem : Good (S.erase i) := by
      intro x hx
      have hix : ⟪a i, x⟫ ≤ b i := by
        by_contra hnot
        apply hn
        refine ⟨x, ?_, lt_of_not_ge hnot⟩
        intro j hj hji
        exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)
      apply hGood x
      intro j hj
      by_cases hji : j = i
      · simpa only [hji] using hix
      · exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    have hcard := hmin (S.erase i) hrem
    have hlt : (S.erase i).card < S.card := Finset.card_erase_lt_of_mem hi
    omega
  let m : ℕ := Fintype.card S
  let E : Fin m ≃ S := (Fintype.equivFin S).symm
  let e : Fin m ↪ Fin n :=
    { toFun := fun j => (E j).val
      inj' := by
        intro j k h
        exact E.injective (Subtype.ext h) }
  have hemem : ∀ j : Fin m, e j ∈ S := fun j => (E j).property
  have hesurj : ∀ i ∈ S, ∃ j : Fin m, e j = i := by
    intro i hi
    refine ⟨E.symm ⟨i, hi⟩, ?_⟩
    change (E (E.symm ⟨i, hi⟩)).val = i
    rw [E.apply_symm_apply]
  have hmn : m ≤ n := by
    have hc := Finset.card_le_card (Finset.subset_univ S)
    simpa only [Finset.card_univ, Fintype.card_fin, m, Fintype.card_coe] using hc
  have hP : Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hpoly a b := by
    ext x
    constructor
    · intro hx
      apply hGood x
      intro i hi
      obtain ⟨j, hj⟩ := hesurj i hi
      simpa only [hj] using hx j
    · intro hx j
      exact hx (e j)
  have hirr : RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hessential (e i) (hemem i)
    refine ⟨x, ?_, hxi⟩
    intro j hji
    exact hx (e j) (hemem j) (fun h => hji (e.injective h))
  have hnonzero : ∀ j : Fin m, a (e j) ≠ 0 := by
    intro j hj0
    obtain ⟨x, _, hx⟩ := hirr j
    change b (e j) < ⟪a (e j), x⟫ at hx
    have hj := hu (e j)
    rw [hj0, inner_zero_left] at hx hj
    linarith
  refine ⟨m, hmn, e, hP, hirr, ?_⟩
  refine ⟨(1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v, ?_⟩
  intro j
  have hju := hu (e j)
  have hjv := hv (e j)
  have hcombo :
      ⟪a (e j), (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v⟫ =
        (⟪a (e j), u⟫ + ⟪a (e j), v⟫) / 2 := by
    simp only [inner_add_right, inner_smul_right]
    ring
  rw [hcombo]
  rcases hsep (e j) (hnonzero j) with hnu | hnv
  · have hlt : ⟪a (e j), u⟫ < b (e j) := lt_of_le_of_ne hju hnu
    linarith
  · have hlt : ⟪a (e j), v⟫ < b (e j) := lt_of_le_of_ne hjv hnv
    linarith


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- A nonempty bounded H-polytope has no nonzero direction annihilated by every
row.  Equivalently, its row-evaluation map is injective. -/
theorem rowMap_injective_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) :
    Function.Injective (rowMap a) := by
  intro p q hpq
  by_contra hpqne
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr hpqne
  have hnorm : 0 < ‖p - q‖ := norm_pos_iff.mpr hdiff
  have hker : rowMap a (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hline : ∀ t : ℝ, x + t • (p - q) ∈ Hpoly a b := by
    intro t i
    have hki : ⟪a i, p - q⟫ = 0 := by
      have hi := congrFun hker i
      simpa [rowMap] using hi
    have hxi := hx i
    simpa [inner_add_right, inner_smul_right, hki] using hxi
  obtain ⟨r, hr⟩ := hb.subset_closedBall x
  let t : ℝ := (r + 1) / ‖p - q‖
  have hr0 : 0 ≤ r := by
    have hball0 := Metric.mem_closedBall.mp (hr hx)
    simpa using hball0
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by linarith) hnorm
  have hball := Metric.mem_closedBall.mp (hr (hline t))
  have hdist : dist (x + t • (p - q)) x = r + 1 := by
    rw [dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp [ne_of_gt hnorm]
  rw [hdist] at hball
  linarith


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Under injectivity of the slack parametrization, every padded slack-coordinate
circuit walk uniquely pulls back to a row-circuit walk in the original H-polytope. -/
theorem slackCircuitWalk_to_rowCircuitWalk
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    SlackCircuitWalk a b L (slack a b u) (slack a b v) →
      RowCircuitWalk a b L u v := by
  classical
  rintro ⟨s, hs0, hsL, hsfeas, hsstep⟩
  let w : ℕ → EuclideanSpace ℝ (Fin d) := fun j =>
    if hj : j ≤ L then Classical.choose (hsfeas j hj).1 else u
  have hwslack : ∀ j (hj : j ≤ L), slack a b (w j) = s j := by
    intro j hj
    dsimp [w]
    rw [dif_pos hj]
    exact (Classical.choose_spec (hsfeas j hj).1).symm
  have hsinj : Function.Injective (slack a b) :=
    slack_injective_of_rowMap_injective a b hinj
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · apply hsinj
    rw [hwslack 0 (Nat.zero_le L), hs0]
  · apply hsinj
    rw [hwslack L le_rfl, hsL]
  · intro j hj
    apply (slack_mem_SlackPoly_iff a b (w j)).mp
    rw [hwslack j hj]
    exact hsfeas j hj
  · intro j hj
    have hjL : j ≤ L := Nat.le_of_lt hj
    have hj1L : j + 1 ≤ L := Nat.succ_le_iff.mpr hj
    rcases hsstep j hj with hstay | hmove
    · left
      apply hsinj
      rw [hwslack j hjL, hwslack (j + 1) hj1L, hstay]
    · right
      apply (rowCircuitStep_iff_slackCircuitStep a b hinj (w j) (w (j + 1))).mpr
      rw [hwslack j hjL, hwslack (j + 1) hj1L]
      exact hmove

/-- Exact equivalence of the original and slack-coordinate circuit-walk notions
once boundedness has supplied injectivity. -/
theorem rowCircuitWalk_iff_slackCircuitWalk
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    RowCircuitWalk a b L u v ↔
      SlackCircuitWalk a b L (slack a b u) (slack a b v) := by
  constructor
  · exact rowCircuitWalk_to_slackCircuitWalk a b hinj L u v
  · exact slackCircuitWalk_to_rowCircuitWalk a b hinj L u v


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch Set Affine

namespace HirschCircuit

/-- The slack parametrization as an affine map. -/
noncomputable def slackAffineMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] (Fin n → ℝ) where
  toFun := slack a b
  linear := -(rowMap a)
  map_vadd' p v := by
    funext i
    change b i - ⟪a i, v + p⟫ = -⟪a i, v⟫ + (b i - ⟪a i, p⟫)
    rw [inner_add_right]
    ring

@[simp] theorem slackAffineMap_apply {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slackAffineMap a b x = slack a b x := rfl

theorem slackAffineMap_injective_of_rowMap_injective {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a)) :
    Function.Injective (slackAffineMap a b) :=
  slack_injective_of_rowMap_injective a b hinj

theorem image_slackAffineMap_Hpoly {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    slackAffineMap a b '' Hpoly a b = SlackPoly a b := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (slack_nonneg_iff_mem_Hpoly a b x).mpr hx⟩
  · rintro ⟨⟨x, rfl⟩, hs⟩
    exact ⟨x, (slack_nonneg_iff_mem_Hpoly a b x).mp hs, rfl⟩

/-- Injective affine maps preserve extreme points of the image. -/
theorem mem_extremePoints_image_of_affine_injective
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hinj : Function.Injective f)
    (S : Set E) (x : E) (hx : x ∈ extremePoints ℝ S) :
    f x ∈ extremePoints ℝ (f '' S) := by
  rw [mem_extremePoints] at hx ⊢
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ hseg
  have hxseg : x ∈ openSegment ℝ x₁ x₂ := by
    have hseg' : f x ∈ f '' openSegment ℝ x₁ x₂ := by
      rw [image_openSegment]
      exact hseg
    rcases hseg' with ⟨z, hz, hzx⟩
    have hzx' : z = x := hinj hzx
    simpa [hzx'] using hz
  rcases hx.2 x₁ hx₁ x₂ hx₂ hxseg with ⟨h₁, h₂⟩
  exact ⟨congrArg f h₁, congrArg f h₂⟩

/-- Vertices of the H-polytope become vertices of its slack image. -/
theorem slack_mem_extremePoints_of_mem_extremePoints {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    slack a b x ∈ extremePoints ℝ (SlackPoly a b) := by
  have h := mem_extremePoints_image_of_affine_injective
    (slackAffineMap a b)
    (slackAffineMap_injective_of_rowMap_injective a b hinj)
    (Hpoly a b) x hx
  rw [image_slackAffineMap_Hpoly a b] at h
  exact h


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- A nonnegative affine slice, independent of any H-presentation. Every
finite-dimensional linear subspace can be presented as a matrix kernel. -/
def StandardSlice {n : ℕ} (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) := {s | s - c ∈ K ∧ ∀ i, 0 ≤ s i}

/-- Sign-reversed elementary direction, as in SlackCircuitStep. Nonzero
rescaling invariance identifies this with the source's forward direction. -/
def StandardCircuitStep {n : ℕ} (K : Submodule ℝ (Fin n → ℝ))
    (c x y : Fin n → ℝ) : Prop :=
  x ∈ StandardSlice K c ∧ y ∈ StandardSlice K c ∧
    IsElementaryIn K (x - y) ∧
    ∀ t : ℝ, 1 < t → x + t • (y - x) ∉ StandardSlice K c

def StandardCircuitWalk {n : ℕ} (K : Submodule ℝ (Fin n → ℝ))
    (c : Fin n → ℝ) (L : ℕ) (u v : Fin n → ℝ) : Prop :=
  ∃ w : ℕ → (Fin n → ℝ), w 0 = u ∧ w L = v ∧
    (∀ j ≤ L, w j ∈ StandardSlice K c) ∧
    ∀ j < L, w j = w (j + 1) ∨ StandardCircuitStep K c (w j) (w (j + 1))

theorem slackPoly_eq_standardSlice {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    SlackPoly a b = StandardSlice (LinearMap.range (rowMap a)) b := by
  ext s
  constructor
  · rintro ⟨⟨x, rfl⟩, hs⟩
    refine ⟨⟨-x, ?_⟩, hs⟩
    funext i
    change ⟪a i, -x⟫ = (b i - ⟪a i, x⟫) - b i
    rw [inner_neg_right]
    ring
  · rintro ⟨⟨g, hg⟩, hs⟩
    refine ⟨⟨-g, ?_⟩, hs⟩
    funext i
    have hi := congrFun hg i
    change ⟪a i, g⟫ = s i - b i at hi
    change s i = b i - ⟪a i, -g⟫
    rw [inner_neg_right]
    linarith

theorem slackCircuitWalk_iff_standardCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (L : ℕ) (u v : Fin n → ℝ) :
    SlackCircuitWalk a b L u v ↔
      StandardCircuitWalk (LinearMap.range (rowMap a)) b L u v := by
  simp only [SlackCircuitWalk, StandardCircuitWalk, SlackCircuitStep,
    StandardCircuitStep, slackPoly_eq_standardSlice]

/-- Complete bounded H-presentation to nonnegative-affine-slice walk bridge. -/
theorem bounded_rowCircuitWalk_iff_standardCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    RowCircuitWalk a b L u v ↔
      StandardCircuitWalk (LinearMap.range (rowMap a)) b L
        (slack a b u) (slack a b v) := by
  exact (rowCircuitWalk_iff_slackCircuitWalk a b
    (rowMap_injective_of_bounded a b hb x hx) L u v).trans
      (slackCircuitWalk_iff_standardCircuitWalk a b L _ _)

theorem rowCircuitWalk_mono {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {L M : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (h : RowCircuitWalk a b L u v) (hLM : L ≤ M) :
    RowCircuitWalk a b M u v := by
  obtain ⟨w, hw0, hwL, hf, hs⟩ := h
  refine ⟨fun j => w (min j L), ?_, ?_, ?_, ?_⟩
  · simpa using hw0
  · simpa only [Nat.min_eq_right hLM] using hwL
  · intro j _
    exact hf _ (Nat.min_le_right _ _)
  · intro j _
    by_cases hj : j < L
    · simpa only [Nat.min_eq_left (Nat.le_of_lt hj),
        Nat.min_eq_left (Nat.succ_le_iff.mpr hj)] using hs j hj
    · left
      change w (min j L) = w (min (j + 1) L)
      rw [Nat.min_eq_right (Nat.le_of_not_gt hj),
        Nat.min_eq_right (by omega : L ≤ j + 1)]

/-- Local source hypothesis, NOT an asserted theorem or an Open platform child.
A cubic relaxation of Natura's standard-form circuit-diameter conclusion.
The source's constructive proof still needs formalization, including the
support-loss reference reset documented in research/NaturaSourceAudit.md. -/
def StandardCubicCircuitBound : Prop :=
  ∃ C : ℕ, ∀ (n : ℕ) (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ),
    ∀ u ∈ Set.extremePoints ℝ (StandardSlice K c),
    ∀ v ∈ Set.extremePoints ℝ (StandardSlice K c),
      StandardCircuitWalk K c (C * n ^ 3) u v

/-- Admission-free conditional theorem with the exact existing Child A result.
It DOES NOT prove its StandardCubicCircuitBound hypothesis. No target imports. -/
theorem cubic_circuit_walk_bound_of_standard
    (hsource : StandardCubicCircuitBound) :
    ∃ C : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
        Hirsch.Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hirsch.Hpoly a b ∧
        Hirsch.RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) ∧
        Hirsch.StrictlyFeasibleRows (fun j => a (e j)) (fun j => b (e j)) ∧
        Hirsch.RowCircuitWalk (fun j => a (e j)) (fun j => b (e j))
          (C * (m + d) ^ 3) u v := by
  obtain ⟨C, hC⟩ := hsource
  refine ⟨C, ?_⟩
  intro d n a b hb u hu v hv hsep
  obtain ⟨m, hmn, e, hP, hirr, hstrict⟩ :=
    exists_irredundant_strict_model d n a b u v hu.1 hv.1 hsep
  let ar := fun j => a (e j)
  let br := fun j => b (e j)
  have hP' : Hpoly ar br = Hpoly a b := hP
  have hb' : Bornology.IsBounded (Hpoly ar br) := by rwa [hP']
  have hu' : u ∈ Set.extremePoints ℝ (Hpoly ar br) := by rwa [hP']
  have hv' : v ∈ Set.extremePoints ℝ (Hpoly ar br) := by rwa [hP']
  have hinj := rowMap_injective_of_bounded ar br hb' u hu'.1
  have hsu := slack_mem_extremePoints_of_mem_extremePoints ar br hinj u hu'
  have hsv := slack_mem_extremePoints_of_mem_extremePoints ar br hinj v hv'
  rw [slackPoly_eq_standardSlice] at hsu hsv
  have hw := hC m (LinearMap.range (rowMap ar)) br (slack ar br u) hsu
    (slack ar br v) hsv
  have hrow := (bounded_rowCircuitWalk_iff_standardCircuitWalk ar br hb' u hu'.1
    (C * m ^ 3) u v).mpr hw
  refine ⟨m, hmn, e, hP, hirr, hstrict, ?_⟩
  exact rowCircuitWalk_mono ar br hrow
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.le_add_right m d) 3))

end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Hirsch

namespace HirschCircuit

/-- A strictly positive maximal augmentation exists when the direction is
nonnegative at every currently zero coordinate and has some negative entry. -/
theorem exists_positive_maximal_nonnegative_step {n : ℕ}
    (x g : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hzero : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ α : ℝ, 0 < α ∧ (∀ i, 0 ≤ x i + α * g i) ∧
      (∃ q, g q < 0 ∧ x q + α * g q = 0) ∧
      ∀ β : ℝ, α < β → ∃ i, x i + β * g i < 0 := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter (fun i => g i < 0)
  have hD : D.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simp [D, hi]⟩
  obtain ⟨q, hqD, hmin⟩ := D.exists_min_image (fun i => x i / (-g i)) hD
  have hq : g q < 0 := (Finset.mem_filter.mp hqD).2
  have hxq : 0 < x q := by
    have hn := hx q
    by_contra hh
    have hz : x q = 0 := le_antisymm (le_of_not_gt hh) hn
    have := hzero q hz
    linarith
  let α : ℝ := x q / (-g q)
  have hα : 0 < α := div_pos hxq (neg_pos.mpr hq)
  have hsat : x q + α * g q = 0 := by
    have he : α * (-g q) = x q := div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hq))
    nlinarith
  refine ⟨α, hα, ?_, ⟨q, hq, hsat⟩, ?_⟩
  · intro i
    by_cases hi : g i < 0
    · have hle : α ≤ x i / (-g i) := hmin i (by simp [D, hi])
      have hmul := (le_div_iff₀ (neg_pos.mpr hi)).mp hle
      nlinarith
    · exact add_nonneg (hx i) (mul_nonneg (le_of_lt hα) (le_of_not_gt hi))
  · intro β hβ
    refine ⟨q, ?_⟩
    have := mul_lt_mul_of_pos_right hβ (neg_pos.mpr hq)
    nlinarith

/-- Every conformal piece of v-x is feasible for step length one. -/
theorem conformal_piece_feasible_at_one {n : ℕ}
    (x v g : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hv : ∀ i, 0 ≤ v i)
    (hg : ConformalTo g (v - x)) : ∀ i, 0 ≤ x i + g i := by
  intro i
  by_cases hi : x i ≤ v i
  · have hgi : 0 ≤ g i := conformalTo_coord_nonneg_of_right_nonneg hg
      (show 0 ≤ (v - x) i by change 0 ≤ v i - x i; linarith)
    linarith [hx i]
  · have hvi : v i ≤ x i := le_of_lt (lt_of_not_ge hi)
    have hgi : g i ≤ 0 := conformalTo_coord_nonpos_of_right_nonpos hg
      (show (v - x) i ≤ 0 by change v i - x i ≤ 0; linarith)
    have habs := (hg i).2
    change |g i| ≤ |v i - x i| at habs
    rw [abs_of_nonpos hgi, abs_of_nonpos (sub_nonpos.mpr hvi)] at habs
    linarith [hv i]

/-- Norm-step trapped-coordinate preservation, parametrized by the circuit-count bound. -/
theorem norm_step_preserves_trapped {n : ℕ}
    (x v g : Fin n → ℝ) (hg : ConformalTo g (v - x))
    (M α : ℝ) (hM : 1 ≤ M) (hα0 : 0 ≤ α) (hαM : α ≤ M)
    (i : Fin n) (hxi : 0 ≤ x i) (htrap : x i ≤ M * v i) :
    x i + α * g i ≤ M * v i := by
  by_cases hi : v i ≤ x i
  · have hgi : g i ≤ 0 := conformalTo_coord_nonpos_of_right_nonpos hg
      (show (v - x) i ≤ 0 by change v i - x i ≤ 0; linarith)
    have := mul_nonpos_of_nonneg_of_nonpos hα0 hgi
    linarith
  · have hvi : x i ≤ v i := le_of_lt (lt_of_not_ge hi)
    have hgi : 0 ≤ g i := conformalTo_coord_nonneg_of_right_nonneg hg
      (show 0 ≤ (v - x) i by change 0 ≤ v i - x i; linarith)
    have habs := (hg i).2
    change |g i| ≤ |v i - x i| at habs
    rw [abs_of_nonneg hgi, abs_of_nonneg (sub_nonneg.mpr hvi)] at habs
    have h1 := mul_le_mul_of_nonneg_left habs hα0
    have h2 := mul_le_mul_of_nonneg_right hαM (sub_nonneg.mpr hvi)
    nlinarith

/-- The zero-support invariant required by the source elimination step. -/
theorem elimination_piece_zero_of_reference_zero {n : ℕ}
    (x r v g : Fin n → ℝ) (ρ lam : ℝ)
    (hg : ConformalTo g
      ((x + (ρ / (1 - ρ)) • (x - r) +
        lam • (v - (x + (ρ / (1 - ρ)) • (x - r)))) - x))
    (i : Fin n) (hx : x i = 0) (hr : r i = 0) (hv : v i = 0) :
    g i = 0 := by
  apply conformalTo_eq_zero_of_right_eq_zero hg
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hx, hr, hv]

/-- Quantitative protection of any zero coordinate. The reference-bound
hypothesis follows from trapped-set preservation or from resetting on support loss. -/
theorem elimination_direction_nonnegative_at_zero {n : ℕ}
    (x r v g : Fin n → ℝ) (M lam γ : ℝ)
    (hv : ∀ i, 0 ≤ v i) (hγ : 0 ≤ γ) (hsmall : γ * M ≤ lam)
    (hg : ConformalTo g (lam • (v - x) + γ • (x - r)))
    (href : ∀ i, x i = 0 → r i ≤ M * v i) :
    ∀ i, x i = 0 → 0 ≤ g i := by
  intro i hi
  apply conformalTo_coord_nonneg_of_right_nonneg hg
  change 0 ≤ lam * (v i - x i) + γ * (x i - r i)
  rw [hi]
  have h1 := mul_le_mul_of_nonneg_left (href i hi) hγ
  have h2 := mul_le_mul_of_nonneg_right hsmall (hv i)
  nlinarith

/-- An outward direction at zero rules out every positive feasible step. -/
theorem no_positive_step_of_negative_at_zero {n : ℕ}
    (x g : Fin n → ℝ) (i : Fin n) (hx : x i = 0) (hg : g i < 0) :
    ∀ α : ℝ, 0 < α → ¬ (∀ j, 0 ≤ x j + α * g j) := by
  intro α hα hfeas
  have hi := hfeas i
  rw [hx, zero_add] at hi
  exact (not_le_of_gt (mul_neg_of_pos_of_neg hα hg)) hi

end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

/-- Turn a positive maximal nonnegative augmentation along an elementary
subspace direction into the exact `StandardCircuitStep` relation. -/
theorem standardCircuitStep_of_maximal_direction {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x g : Fin n → ℝ) (α : ℝ)
    (hx : x ∈ StandardSlice K c)
    (hgelem : IsElementaryIn K g)
    (hα : 0 < α)
    (hfeas : ∀ i, 0 ≤ x i + α * g i)
    (hmax : ∀ β : ℝ, α < β → ∃ i, x i + β * g i < 0) :
    StandardCircuitStep K c x (x + α • g) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  refine ⟨hx, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hK : (x + α • g) - c = (x - c) + α • g := by
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hK]
      exact K.add_mem hx.1 (K.smul_mem α hgelem.2.1)
    · intro i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hfeas i
  · have hscale : x - (x + α • g) = (-α) • g := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hscale]
    exact isElementaryIn_smul K hgelem (neg_ne_zero.mpr hαne)
  · intro t ht hmem
    have hβ : α < t * α := by
      nlinarith [hα]
    obtain ⟨i, hi⟩ := hmax (t * α) hβ
    have hnonneg := hmem.2 i
    have heq :
        (x + t • ((x + α • g) - x)) i = x i + (t * α) * g i := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [heq] at hnonneg
    linarith

/-- If an elementary direction is safe at every currently zero coordinate and
negative somewhere, its finite blocking ratio gives a genuine positive maximal
`StandardCircuitStep`. -/
theorem exists_standardCircuitStep_along_elementary {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x g : Fin n → ℝ)
    (hx : x ∈ StandardSlice K c)
    (hgelem : IsElementaryIn K g)
    (hzero : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ α : ℝ, 0 < α ∧
      StandardCircuitStep K c x (x + α • g) ∧
      (∀ i, 0 ≤ x i + α * g i) ∧
      (∃ q, g q < 0 ∧ x q + α * g q = 0) := by
  obtain ⟨α, hα, hfeas, hsat, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero hneg
  refine ⟨α, hα, ?_, hfeas, hsat⟩
  exact standardCircuitStep_of_maximal_direction K c x g α hx hgelem hα hfeas hmax


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set

namespace HirschCircuit

/-- In the nonnegative affine slice through an extreme target `v`, a feasible
point that vanishes everywhere outside the positive support of `v` is `v`.
This is the target-support uniqueness fact used by the support-safe routing
argument. -/
theorem eq_target_of_zero_off_support {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ))
    (v y : Fin n → ℝ)
    (hv : v ∈ extremePoints ℝ (StandardSlice K v))
    (hy : y ∈ StandardSlice K v)
    (hsupp : ∀ i, v i = 0 → y i = 0) :
    y = v := by
  by_contra hne
  let h : Fin n → ℝ := y - v
  have hh0 : h ≠ 0 := by
    intro hz
    apply hne
    funext i
    have hi := congrFun hz i
    dsimp [h] at hi
    linarith
  have hhK : h ∈ K := by
    simpa [h] using hy.1
  have hvFeas : v ∈ StandardSlice K v := extremePoints_subset hv
  have hvNonneg : ∀ i, 0 ≤ v i := hvFeas.2
  have hyNonneg : ∀ i, 0 ≤ y i := hy.2

  let D : Finset (Fin n) := Finset.univ.filter (fun i => 0 < h i)
  obtain ⟨eps, heps, hback⟩ : ∃ eps : ℝ, 0 < eps ∧
      ∀ i, 0 ≤ v i - eps * h i := by
    by_cases hD : D.Nonempty
    · obtain ⟨q, hqD, hmin⟩ :=
        D.exists_min_image (fun i => v i / h i) hD
      have hqpos : 0 < h q := (Finset.mem_filter.mp hqD).2
      have hvqpos : 0 < v q := by
        have hvq := hvNonneg q
        by_contra hnot
        have hvq0 : v q = 0 := le_antisymm (le_of_not_gt hnot) hvq
        have hyq0 := hsupp q hvq0
        dsimp [h] at hqpos
        linarith
      let eps : ℝ := v q / h q
      have heps : 0 < eps := div_pos hvqpos hqpos
      refine ⟨eps, heps, ?_⟩
      intro i
      by_cases hi : 0 < h i
      · have hiD : i ∈ D := by simp [D, hi]
        have hle : eps ≤ v i / h i := by
          simpa [eps] using hmin i hiD
        have hmul := (le_div_iff₀ hi).mp hle
        linarith
      · have hhi : h i ≤ 0 := le_of_not_gt hi
        have hmul : eps * h i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt heps) hhi
        linarith [hvNonneg i]
    · refine ⟨1, zero_lt_one, ?_⟩
      intro i
      have hiNot : i ∉ D := by
        intro hiD
        exact hD ⟨i, hiD⟩
      have hhi : h i ≤ 0 := by
        have : ¬ 0 < h i := by simpa [D] using hiNot
        exact le_of_not_gt this
      linarith [hvNonneg i]

  let w : Fin n → ℝ := v - eps • h
  have hwK : w - v ∈ K := by
    have heq : w - v = (-eps) • h := by
      funext i
      simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact K.smul_mem _ hhK
  have hwNonneg : ∀ i, 0 ≤ w i := by
    intro i
    simpa [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hback i
  have hw : w ∈ StandardSlice K v := ⟨hwK, hwNonneg⟩

  have hseg : v ∈ openSegment ℝ y w := by
    rw [mem_openSegment_iff_div]
    refine ⟨eps, 1, heps, zero_lt_one, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w, h, Pi.sub_apply]
    have hden : eps + 1 ≠ 0 := ne_of_gt (by linarith : 0 < eps + 1)
    field_simp [hden]
    ring

  rw [mem_extremePoints] at hv
  have hyv := (hv.2 y hy w hw hseg).1
  exact hne hyv


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

/-- Coordinates that have made permanent phase progress toward a nonnegative
target: target-zero coordinates already at zero, and target-positive
coordinates already below the `M*v_i` trapped threshold. -/
noncomputable def phaseProgressSet {n : ℕ}
    (M : ℝ) (v x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    if v i = 0 then x i = 0 else x i ≤ M * v i

@[simp] theorem mem_phaseProgressSet {n : ℕ}
    (M : ℝ) (v x : Fin n → ℝ) (i : Fin n) :
    i ∈ phaseProgressSet M v x ↔
      (if v i = 0 then x i = 0 else x i ≤ M * v i) := by
  simp [phaseProgressSet]

theorem phaseProgressSet_card_le {n : ℕ}
    (M : ℝ) (v x : Fin n → ℝ) :
    (phaseProgressSet M v x).card ≤ n := by
  have hsub : phaseProgressSet M v x ⊆ Finset.univ := Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  simpa using hcard

/-- Pointwise preservation of target-zero coordinates and trapped coordinates
makes the phase-progress set monotone. -/
theorem phaseProgressSet_mono {n : ℕ}
    (M : ℝ) (v x y : Fin n → ℝ)
    (hzero : ∀ i, v i = 0 → x i = 0 → y i = 0)
    (htrap : ∀ i, v i ≠ 0 → x i ≤ M * v i → y i ≤ M * v i) :
    phaseProgressSet M v x ⊆ phaseProgressSet M v y := by
  intro i hi
  simp only [mem_phaseProgressSet] at hi ⊢
  by_cases hv0 : v i = 0
  · simp only [hv0, if_pos]
    exact hzero i hv0 (by simpa [hv0] using hi)
  · simp only [hv0, if_neg]
    exact htrap i hv0 (by simpa [hv0] using hi)

/-- A newly zeroed target-zero coordinate or a newly trapped target-positive
coordinate strictly enlarges the finite progress set. -/
theorem phaseProgressSet_ssubset_of_event {n : ℕ}
    (M : ℝ) (v x y : Fin n → ℝ)
    (hmono : phaseProgressSet M v x ⊆ phaseProgressSet M v y)
    (hevent : ∃ i,
      (v i = 0 ∧ x i ≠ 0 ∧ y i = 0) ∨
      (v i ≠ 0 ∧ ¬ x i ≤ M * v i ∧ y i ≤ M * v i)) :
    phaseProgressSet M v x ⊂ phaseProgressSet M v y := by
  obtain ⟨i, hi⟩ := hevent
  refine ssubset_of_ne_of_subset ?_ hmono
  intro heq
  have hiff : i ∈ phaseProgressSet M v x ↔ i ∈ phaseProgressSet M v y := by
    rw [heq]
  rcases hi with ⟨hv0, hxi, hy0⟩ | ⟨hv0, hxi, hyi⟩
  · have hyMem : i ∈ phaseProgressSet M v y := by
      simp [mem_phaseProgressSet, hv0, hy0]
    have hxMem := hiff.mpr hyMem
    simp [mem_phaseProgressSet, hv0] at hxMem
    exact hxi hxMem
  · have hyMem : i ∈ phaseProgressSet M v y := by
      simp [mem_phaseProgressSet, hv0, hyi]
    have hxMem := hiff.mpr hyMem
    simp [mem_phaseProgressSet, hv0] at hxMem
    exact hxi hxMem

/-- Equal phase-progress sets synchronize the two invariants needed by the
support-safe reference rule. -/
theorem same_phase_zero_iff {n : ℕ}
    (M : ℝ) (v r x : Fin n → ℝ)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x)
    (i : Fin n) (hv0 : v i = 0) :
    r i = 0 ↔ x i = 0 := by
  have hiff : i ∈ phaseProgressSet M v r ↔ i ∈ phaseProgressSet M v x := by
    rw [heq]
  simpa [mem_phaseProgressSet, hv0] using hiff

theorem same_phase_trapped_iff {n : ℕ}
    (M : ℝ) (v r x : Fin n → ℝ)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x)
    (i : Fin n) (hv0 : v i ≠ 0) :
    r i ≤ M * v i ↔ x i ≤ M * v i := by
  have hiff : i ∈ phaseProgressSet M v r ↔ i ∈ phaseProgressSet M v x := by
    rw [heq]
  simpa [mem_phaseProgressSet, hv0] using hiff

/-- At a target-positive coordinate, a zero current value is necessarily
trapped, hence the phase reference was already trapped if no event occurred. -/
theorem same_phase_reference_trapped_of_current_zero {n : ℕ}
    (M : ℝ) (v r x : Fin n → ℝ)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x)
    (hM : 0 ≤ M) (hv : ∀ i, 0 ≤ v i)
    (i : Fin n) (hxi : x i = 0) :
    r i ≤ M * v i := by
  by_cases hv0 : v i = 0
  · have hr0 := (same_phase_zero_iff M v r x heq i hv0).2 hxi
    rw [hr0, hv0]
    simp
  · apply (same_phase_trapped_iff M v r x heq i hv0).2
    rw [hxi]
    exact mul_nonneg hM (hv i)

/-- If every coordinate has entered the finite progress set, then all
coordinates outside the positive support of `v` are zero. Extremality then
forces the current point to be the target. -/
theorem eq_target_of_full_phase_progress {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ))
    (M : ℝ) (v x : Fin n → ℝ)
    (hvext : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hx : x ∈ StandardSlice K v)
    (hfull : phaseProgressSet M v x = Finset.univ) :
    x = v := by
  apply eq_target_of_zero_off_support K v x hvext hx
  intro i hv0
  have hi : i ∈ phaseProgressSet M v x := by simp [hfull]
  simpa [mem_phaseProgressSet, hv0] using hi

/-- Strict progress can occur at most `n` times in any chain of phase-progress
sets. This cardinal form is the global phase counter used by the route proof. -/
theorem phase_progress_card_strict {n : ℕ}
    (M : ℝ) (v x y : Fin n → ℝ)
    (hstrict : phaseProgressSet M v x ⊂ phaseProgressSet M v y) :
    (phaseProgressSet M v x).card < (phaseProgressSet M v y).card :=
  Finset.card_lt_card hstrict


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace HirschCircuit

private theorem list_sum_le_length_mul
    {α : Type*} (xs : List α) (f : α → ℝ) (c : ℝ)
    (h : ∀ x ∈ xs, f x ≤ c) :
    (xs.map f).sum ≤ (xs.length : ℝ) * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : f a ≤ c := h a (by simp)
      have htail : ∀ x ∈ xs, f x ≤ c := by
        intro x hx
        exact h x (by simp [hx])
      have hih := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      linarith

/-- If at most `M` real scores sum to a positive quantity `W`, some score is at
least the average lower bound `W/M`. This is the finite selector used for both
norm-reduction and elimination circuit choices. -/
theorem exists_mem_ge_average
    {α : Type*} (xs : List α) (f : α → ℝ) (M : ℕ) (W : ℝ)
    (hM : 0 < M) (hlen : xs.length ≤ M) (hW : 0 < W)
    (hsum : (xs.map f).sum = W) :
    ∃ x ∈ xs, W / (M : ℝ) ≤ f x := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ x ∈ xs, f x < W / (M : ℝ) := hnone
  have hxs : xs ≠ [] := by
    intro hx
    subst xs
    simp at hsum
    linarith
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil hxs
  have ha : f a < W / (M : ℝ) := hall a (by simp)
  have htail : ∀ x ∈ tail, f x ≤ W / (M : ℝ) := by
    intro x hx
    exact le_of_lt (hall x (by simp [hx]))
  have htailSum := list_sum_le_length_mul tail f (W / (M : ℝ)) htail
  have hsumlt : (List.map f (a :: tail)).sum <
      ((a :: tail).length : ℝ) * (W / (M : ℝ)) := by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    linarith
  have hlenR : ((a :: tail).length : ℝ) ≤ (M : ℝ) := by exact_mod_cast hlen
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have havg : 0 < W / (M : ℝ) := div_pos hW hMR
  have hupper : ((a :: tail).length : ℝ) * (W / (M : ℝ)) ≤ W := by
    have hmul := mul_le_mul_of_nonneg_right hlenR (le_of_lt havg)
    have hcancel : (M : ℝ) * (W / (M : ℝ)) = W := by
      field_simp [ne_of_gt hMR]
    rwa [hcancel] at hmul
  linarith [hsumlt, hupper, hsum]

/-- A nonempty exact decomposition of a nonzero vector has a nonempty list of
pieces. -/
theorem list_nonempty_of_sum_ne_zero {α : Type*} [AddMonoid α]
    (xs : List α) (h : xs.sum ≠ 0) : xs ≠ [] := by
  intro hx
  subst xs
  simp at h


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

/-- Target-zero coordinates live relative to the fixed phase reference. -/
noncomputable def liveZeroSet {n : ℕ} (v r : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => v i = 0 ∧ r i ≠ 0

@[simp] theorem mem_liveZeroSet {n : ℕ}
    (v r : Fin n → ℝ) (i : Fin n) :
    i ∈ liveZeroSet v r ↔ v i = 0 ∧ r i ≠ 0 := by
  simp [liveZeroSet]

/-- Fixed-reference potential on the live target-zero coordinates. -/
noncomputable def phasePotential {n : ℕ}
    (v r x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ liveZeroSet v r, x i / r i

/-- Decrease in the fixed-reference potential per unit of augmentation. -/
noncomputable def normScore {n : ℕ}
    (v r g : Fin n → ℝ) : ℝ :=
  ∑ i ∈ liveZeroSet v r, (-g i) / r i

theorem liveZero_ref_pos {n : ℕ}
    {v r : Fin n → ℝ} (hr : ∀ i, 0 ≤ r i)
    {i : Fin n} (hi : i ∈ liveZeroSet v r) : 0 < r i := by
  have hne := ((mem_liveZeroSet v r i).mp hi).2
  exact lt_of_le_of_ne (hr i) (Ne.symm hne)

theorem phasePotential_nonneg {n : ℕ}
    (v r x : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ phasePotential v r x := by
  unfold phasePotential
  exact Finset.sum_nonneg fun i _ => div_nonneg (hx i) (hr i)

theorem normScore_add {n : ℕ}
    (v r g h : Fin n → ℝ) :
    normScore v r (g + h) = normScore v r g + normScore v r h := by
  unfold normScore
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem normScore_zero {n : ℕ} (v r : Fin n → ℝ) :
    normScore v r 0 = 0 := by
  simp [normScore]

theorem normScore_list_sum {n : ℕ}
    (v r : Fin n → ℝ) (gs : List (Fin n → ℝ)) :
    normScore v r gs.sum = (gs.map (normScore v r)).sum := by
  induction gs with
  | nil => simp [normScore_zero]
  | cons g gs ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [normScore_add, ih]

theorem normScore_target_sub_eq_potential {n : ℕ}
    (v r x : Fin n → ℝ) :
    normScore v r (v - x) = phasePotential v r x := by
  unfold normScore phasePotential
  apply Finset.sum_congr rfl
  intro i hi
  have hv0 := ((mem_liveZeroSet v r i).mp hi).1
  simp only [Pi.sub_apply, hv0, zero_sub, neg_neg]

theorem normScore_nonneg_of_conformal {n : ℕ}
    (v r x g : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hx : ∀ i, 0 ≤ x i)
    (hg : ConformalTo g (v - x)) :
    0 ≤ normScore v r g := by
  unfold normScore
  apply Finset.sum_nonneg
  intro i hi
  have himem := (mem_liveZeroSet v r i).mp hi
  have hgi : g i ≤ 0 := by
    apply conformalTo_coord_nonpos_of_right_nonpos hg
    change v i - x i ≤ 0
    rw [himem.1]
    linarith [hx i]
  exact div_nonneg (neg_nonneg.mpr hgi) (hr i)

theorem phasePotential_step {n : ℕ}
    (v r x g : Fin n → ℝ) (α : ℝ) :
    phasePotential v r (x + α • g) =
      phasePotential v r x - α * normScore v r g := by
  unfold phasePotential normScore
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A genuine positive maximal elementary step, with `1 ≤ α ≤ M`, contracts
fixed-reference potential and preserves the support-safe phase progress set.
The selected direction belongs to the original subspace, not a smaller cone. -/
theorem exists_norm_reduction_step {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ))
    (M : ℕ) (hM : 0 < M) (hnM : n ≤ M)
    (v r x : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i)
    (hx : x ∈ StandardSlice K v)
    (hW : 0 < phasePotential v r x) :
    ∃ y g : Fin n → ℝ, ∃ α : ℝ,
      0 < α ∧ 1 ≤ α ∧ α ≤ (M : ℝ) ∧
      StandardCircuitStep K v x y ∧
      y = x + α • g ∧
      0 ≤ phasePotential v r y ∧
      phasePotential v r y ≤
        (1 - 1 / (M : ℝ)) * phasePotential v r x ∧
      phaseProgressSet (M : ℝ) v x ⊆ phaseProgressSet (M : ℝ) v y ∧
      ∀ i, v i = 0 → y i ≤ x i := by
  classical
  have hzK : v - x ∈ K := by
    have hneg := K.neg_mem hx.1
    simpa only [neg_sub] using hneg
  obtain ⟨gs, hlenN, hall, hsum⟩ :=
    exists_elementary_conformal_decomposition_le_n K (v - x) hzK
  have hlenM : gs.length ≤ M := hlenN.trans hnM
  let W : ℝ := phasePotential v r x
  have hscoreSum : (gs.map (normScore v r)).sum = W := by
    change (gs.map (normScore v r)).sum = phasePotential v r x
    rw [← normScore_list_sum, hsum, normScore_target_sub_eq_potential]
  obtain ⟨g, hgmem, hscore⟩ :=
    exists_mem_ge_average gs (normScore v r) M W hM hlenM hW hscoreSum
  obtain ⟨hgelem, hgconf⟩ := hall g hgmem
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have havgpos : 0 < W / (M : ℝ) := div_pos hW hMr
  have hSpos : 0 < normScore v r g := lt_of_lt_of_le havgpos hscore
  have hneg : ∃ i, g i < 0 := by
    by_contra hn
    push Not at hn
    have hnonpos : normScore v r g ≤ 0 := by
      unfold normScore
      exact Finset.sum_nonpos fun i _ =>
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hn i)) (hr i)
    linarith
  have hzero : ∀ i, x i = 0 → 0 ≤ g i := by
    intro i hxi
    apply conformalTo_coord_nonneg_of_right_nonneg hgconf
    change 0 ≤ v i - x i
    simpa only [hxi, sub_zero] using hv i
  obtain ⟨α, hα, hfeas, _hsat, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero hneg
  let y : Fin n → ℝ := x + α • g
  have hstep : StandardCircuitStep K v x y :=
    standardCircuitStep_of_maximal_direction K v x g α hx hgelem hα hfeas hmax
  have honeFeas := conformal_piece_feasible_at_one x v g hx.2 hv hgconf
  have hα1 : 1 ≤ α := by
    by_contra hn
    obtain ⟨i, hi⟩ := hmax 1 (lt_of_not_ge hn)
    have hfi := honeFeas i
    linarith
  have hWnew : 0 ≤ phasePotential v r y :=
    phasePotential_nonneg v r y hr hstep.2.1.2
  have hupdate : phasePotential v r y = W - α * normScore v r g :=
    phasePotential_step v r x g α
  have hαSle : α * normScore v r g ≤ W := by
    rw [hupdate] at hWnew
    linarith
  have hαavg : α * (W / (M : ℝ)) ≤ W :=
    (mul_le_mul_of_nonneg_left hscore (le_of_lt hα)).trans hαSle
  have hcancel : (W / (M : ℝ)) * (M : ℝ) = W :=
    div_mul_cancel₀ W (ne_of_gt hMr)
  have hαM : α ≤ (M : ℝ) := by
    nlinarith only [hαavg, hcancel, havgpos]
  have hSleαS : normScore v r g ≤ α * normScore v r g := by
    nlinarith only [hα1, hSpos]
  have havgleαS : W / (M : ℝ) ≤ α * normScore v r g := hscore.trans hSleαS
  have hcontract : phasePotential v r y ≤
      (1 - 1 / (M : ℝ)) * phasePotential v r x := by
    rw [hupdate]
    change W - α * normScore v r g ≤ (1 - 1 / (M : ℝ)) * W
    calc
      W - α * normScore v r g ≤ W - W / (M : ℝ) := sub_le_sub_left havgleαS W
      _ = (1 - 1 / (M : ℝ)) * W := by simp only [div_eq_mul_inv]; ring
  have hM1nat : 1 ≤ M := hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1nat
  have hprogress : phaseProgressSet (M : ℝ) v x ⊆ phaseProgressSet (M : ℝ) v y := by
    apply phaseProgressSet_mono
    · intro i hvi hxi
      have hz0 : (v - x) i = 0 := by simp [Pi.sub_apply, hvi, hxi]
      have hgi0 := conformalTo_eq_zero_of_right_eq_zero hgconf hz0
      change x i + α * g i = 0
      rw [hxi, hgi0]
      ring
    · intro i _ htrap
      exact norm_step_preserves_trapped x v g hgconf (M : ℝ) α hM1
        (le_of_lt hα) hαM i (hx.2 i) htrap
  have hzeroMono : ∀ i, v i = 0 → y i ≤ x i := by
    intro i hvi
    have hgi : g i ≤ 0 := by
      apply conformalTo_coord_nonpos_of_right_nonpos hgconf
      change v i - x i ≤ 0
      rw [hvi]
      linarith [hx.2 i]
    change x i + α * g i ≤ x i
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hα) hgi
    linarith
  exact ⟨y, g, α, hα, hα1, hαM, hstep, rfl, hWnew, hcontract, hprogress, hzeroMono⟩

end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace HirschCircuit

/-- A scalar conformal piece lies between zero and the full displacement. -/
def ScalarConformalPiece (g delta : ℝ) : Prop :=
  (0 ≤ g ∧ g ≤ delta) ∨ (delta ≤ g ∧ g ≤ 0)

theorem scalarConformalPiece_of_sign_abs
    (g delta : ℝ) (hsign : 0 ≤ g * delta) (habs : |g| ≤ |delta|) :
    ScalarConformalPiece g delta := by
  rcases le_total 0 delta with hd | hd
  · by_cases hd0 : delta = 0
    · have hg : g = 0 := by
        apply abs_eq_zero.mp
        apply le_antisymm
        · simpa only [hd0, abs_zero] using habs
        · exact abs_nonneg g
      left
      simp [hg, hd0]
    · have hdp : 0 < delta := by
        rcases lt_or_eq_of_le hd with hp | he
        · exact hp
        · exact (hd0 he.symm).elim
      have hg : 0 ≤ g := by
        by_contra hn
        have hn' : g < 0 := lt_of_not_ge hn
        have hneg := mul_neg_of_neg_of_pos hn' hdp
        linarith
      left
      refine ⟨hg, ?_⟩
      simpa only [abs_of_nonneg hg, abs_of_nonneg hd] using habs
  · by_cases hd0 : delta = 0
    · have hg : g = 0 := by
        apply abs_eq_zero.mp
        apply le_antisymm
        · simpa only [hd0, abs_zero] using habs
        · exact abs_nonneg g
      right
      simp [hg, hd0]
    · have hdn : delta < 0 := lt_of_le_of_ne hd hd0
      have hg : g ≤ 0 := by
        by_contra hn
        have hn' : 0 < g := lt_of_not_ge hn
        have hneg := mul_neg_of_pos_of_neg hn' hdn
        linarith
      right
      refine ⟨?_, hg⟩
      rw [abs_of_nonpos hg, abs_of_nonpos hd] at habs
      linarith

/-- Bound the full scaled displacement before considering a conformal piece.
This is purely scalar algebra; no circuit, rank, or vertex assumption occurs. -/
theorem elimination_full_displacement_bounds
    (M v x r lam eta : ℝ)
    (hM : 2 ≤ M) (hv : 0 ≤ v) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hxM : x ≤ M * v) (hrM : r ≤ M * v)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hlamM : M * lam ≤ 1 / 2) (hetaM : M * eta ≤ lam) :
    x / 2 ≤ x + M * (lam * (v - x) + eta * (x - r)) ∧
    x + M * (lam * (v - x) + eta * (x - r)) ≤ M * v := by
  have hM0 : 0 ≤ M := by linarith
  have hMeta : 0 ≤ M * eta := mul_nonneg hM0 heta
  let c : ℝ := 1 - M * lam + M * eta
  have hc : 1 / 2 ≤ c := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := by linarith
  have hidentity :
      x + M * (lam * (v - x) + eta * (x - r)) =
        c * x + M * lam * v - M * eta * r := by
    dsimp [c]
    ring
  rw [hidentity]
  constructor
  · have hcx := mul_le_mul_of_nonneg_right hc hx
    have hrr := mul_le_mul_of_nonneg_left hrM hMeta
    have hremaining : 0 ≤ M * ((lam - M * eta) * v) :=
      mul_nonneg hM0 (mul_nonneg (sub_nonneg.mpr hetaM) hv)
    nlinarith only [hcx, hrr, hremaining]
  · have hcx := mul_le_mul_of_nonneg_left hxM hc0
    have hdrop : 0 ≤ M * eta * r := mul_nonneg hMeta hr
    have hbracket : (1 - M) * lam + M * eta ≤ 0 := by
      have haux : 0 ≤ (M - 2) * lam :=
        mul_nonneg (sub_nonneg.mpr hM) hlam
      nlinarith only [haux, hetaM]
    have hcorrection :
        (M * v) * ((1 - M) * lam + M * eta) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hM0 hv) hbracket
    calc
      c * x + M * lam * v - M * eta * r ≤ c * (M * v) + M * lam * v := by
        linarith only [hcx, hdrop]
      _ = M * v + (M * v) * ((1 - M) * lam + M * eta) := by
        dsimp [c]
        ring
      _ ≤ M * v := by linarith only [hcorrection]

/-- A trapped coordinate cannot block an elimination augmentation of size at
most M: if it starts positive it stays at least half as large, and it remains
below M times its target value. -/
theorem elimination_conformal_coordinate_bounds
    (M v x r lam eta g alpha : ℝ)
    (hM : 2 ≤ M) (hv : 0 ≤ v) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hxM : x ≤ M * v) (hrM : r ≤ M * v)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hlamM : M * lam ≤ 1 / 2) (hetaM : M * eta ≤ lam)
    (hpiece : ScalarConformalPiece g (lam * (v - x) + eta * (x - r)))
    (halpha : 0 ≤ alpha) (halphaM : alpha ≤ M) :
    x / 2 ≤ x + alpha * g ∧ x + alpha * g ≤ M * v := by
  obtain ⟨hlower, hupper⟩ := elimination_full_displacement_bounds
    M v x r lam eta hM hv hx hr hxM hrM hlam heta hlamM hetaM
  have hM0 : 0 ≤ M := by linarith
  rcases hpiece with ⟨hg0, hgd⟩ | ⟨hdg, hg0⟩
  · have hstep0 : 0 ≤ alpha * g := mul_nonneg halpha hg0
    have hstepM := mul_le_mul_of_nonneg_right halphaM hg0
    have hMg := mul_le_mul_of_nonneg_left hgd hM0
    constructor <;> linarith
  · have hstep0 : alpha * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos halpha hg0
    have hstepM := mul_le_mul_of_nonpos_right halphaM hg0
    have hMg := mul_le_mul_of_nonneg_left hdg hM0
    constructor <;> linarith

/-- The auxiliary extrapolation coefficient is bounded by rho whenever
0 ≤ rho ≤ lambda ≤ 1 and rho < 1. -/
theorem extrapolation_eta_bounds
    (lam rho : ℝ) (hlam : lam ≤ 1) (hrho : 0 ≤ rho)
    (hrholam : rho ≤ lam) (hrho1 : rho < 1) :
    0 ≤ (1 - lam) * rho / (1 - rho) ∧
    (1 - lam) * rho / (1 - rho) ≤ rho := by
  have hden : 0 < 1 - rho := sub_pos.mpr hrho1
  constructor
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hlam) hrho) (le_of_lt hden)
  · apply (div_le_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_right hrholam hrho
    nlinarith only [hmul]

/-- The simpler norm-reduction step also preserves the trapped upper bound. -/
theorem norm_step_trapped_upper
    (M v x g alpha : ℝ)
    (hM : 1 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M * v)
    (hpiece : ScalarConformalPiece g (v - x))
    (halpha : 0 ≤ alpha) (halphaM : alpha ≤ M) :
    x + alpha * g ≤ M * v := by
  have hM0 : 0 ≤ M := by linarith
  rcases hpiece with ⟨hg0, hgd⟩ | ⟨_, hg0⟩
  · have ha := mul_le_mul_of_nonneg_right halphaM hg0
    have hg := mul_le_mul_of_nonneg_left hgd hM0
    have hnonneg : 0 ≤ (M - 1) * x := mul_nonneg (sub_nonneg.mpr hM) hx
    nlinarith only [ha, hg, hnonneg]
  · have ha := mul_nonpos_of_nonneg_of_nonpos halpha hg0
    linarith

/-- Integer envelope for n event phases and at most 4 M^2+1 steps per phase. -/
theorem event_budget_le_cubic
    (n M : ℕ) (hn : 1 ≤ n) (hM : M ≤ 2 * n) :
    n * (4 * M ^ 2 + 1) ≤ 17 * n ^ 3 := by
  have hsq := Nat.mul_le_mul hM hM
  have hnsq := Nat.mul_le_mul hn hn
  have hstage : 4 * M ^ 2 + 1 ≤ 17 * n ^ 2 := by
    nlinarith only [hsq, hnsq]
  calc
    n * (4 * M ^ 2 + 1) ≤ n * (17 * n ^ 2) := Nat.mul_le_mul_left n hstage
    _ = 17 * n ^ 3 := by ring


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

private theorem list_neg_eval_sum {n : ℕ}
    (gs : List (Fin n → ℝ)) (q : Fin n) :
    (gs.map fun g => -g q).sum = -(gs.sum q) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply]
      rw [ih]
      ring

/-- The support-safe elimination step. The hypotheses describe its scalar
parameters and displacement, not an assumed step or progress conclusion.
A conformal elementary piece is selected by averaging, augmented maximally,
and proved to create a new target-zero or trapped coordinate. -/
theorem exists_support_safe_elimination_step {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ)
    (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r x : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x)
    (lam eta : ℝ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hlamM : (M : ℝ) * lam ≤ 1 / 2) (hetaM : (M : ℝ) * eta ≤ lam)
    (hN : ∀ i, v i = 0 → lam * (v i - x i) + eta * (x i - r i) ≤ 0)
    (q : Fin n) (hxq : 0 < x q)
    (hq : lam * (v q - x q) + eta * (x q - r q) = -x q) :
    ∃ y : Fin n → ℝ,
      StandardCircuitStep K v x y ∧
      phaseProgressSet (M : ℝ) v x ⊂ phaseProgressSet (M : ℝ) v y ∧
      (∀ i, v i = 0 → y i ≤ x i) ∧
      ∀ i, v i ≠ 0 → x i ≤ (M : ℝ) * v i → x i / 2 ≤ y i := by
  classical
  have hMpos : 0 < M := by omega
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMrpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMr0 : (0 : ℝ) ≤ (M : ℝ) := le_of_lt hMrpos
  let delta : Fin n → ℝ := lam • (v - x) + eta • (x - r)
  have hxr : x - r ∈ K := by
    have hid : x - r = (x - v) - (r - v) := by abel
    rw [hid]
    exact K.sub_mem hx.1 hr.1
  have hvx : v - x ∈ K := by simpa only [neg_sub] using K.neg_mem hx.1
  have hdelta : delta ∈ K := K.add_mem (K.smul_mem lam hvx) (K.smul_mem eta hxr)
  have hdeltaq : delta q = -x q := hq
  obtain ⟨gs, hlen, hall, hsum⟩ :=
    exists_elementary_conformal_decomposition_le_n K delta hdelta
  have hsumq : (gs.map fun g => -g q).sum = x q := by
    rw [list_neg_eval_sum, hsum, hdeltaq, neg_neg]
  obtain ⟨g, hgmem, hscore⟩ :=
    exists_mem_ge_average gs (fun g => -g q) M (x q) hMpos (hlen.trans hnM) hxq hsumq
  obtain ⟨hgelem, hgconf⟩ := hall g hgmem
  have havg : 0 < x q / (M : ℝ) := div_pos hxq hMrpos
  have hgq : g q < 0 := by linarith
  have hzero : ∀ i, x i = 0 → 0 ≤ g i := by
    intro i hxi
    apply conformalTo_coord_nonneg_of_right_nonneg hgconf
    have href := same_phase_reference_trapped_of_current_zero
      (M : ℝ) v r x heq hMr0 hv i hxi
    have h1 := mul_le_mul_of_nonneg_left href heta
    have h2 := mul_le_mul_of_nonneg_right hetaM (hv i)
    change 0 ≤ lam * (v i - x i) + eta * (x i - r i)
    rw [hxi]
    nlinarith only [h1, h2]
  obtain ⟨alpha, ha, hfeas, hsat, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero ⟨q, hgq⟩
  let y : Fin n → ℝ := x + alpha • g
  have hstep : StandardCircuitStep K v x y :=
    standardCircuitStep_of_maximal_direction K v x g alpha hx hgelem ha hfeas hmax
  have haM : alpha ≤ (M : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hscore (le_of_lt ha)
    have hqfeas := hfeas q
    have hcancel : (x q / (M : ℝ)) * (M : ℝ) = x q :=
      div_mul_cancel₀ _ (ne_of_gt hMrpos)
    nlinarith only [hmul, hqfeas, hcancel, havg]
  have htrap : ∀ i, v i ≠ 0 → x i ≤ (M : ℝ) * v i →
      x i / 2 ≤ y i ∧ y i ≤ (M : ℝ) * v i := by
    intro i hvi hxi
    have href := (same_phase_trapped_iff (M : ℝ) v r x heq i hvi).mpr hxi
    have hpiece := scalarConformalPiece_of_sign_abs (g i) (delta i)
      (hgconf i).1 (hgconf i).2
    exact elimination_conformal_coordinate_bounds (M : ℝ) (v i) (x i) (r i)
      lam eta (g i) alpha hMr (hv i) (hx.2 i) (hr.2 i) hxi href
      hlam heta hlamM hetaM hpiece (le_of_lt ha) haM
  have hNmono : ∀ i, v i = 0 → y i ≤ x i := by
    intro i hvi
    have hgi : g i ≤ 0 := conformalTo_coord_nonpos_of_right_nonpos hgconf (hN i hvi)
    change x i + alpha * g i ≤ x i
    have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hgi
    linarith
  have hprogress : phaseProgressSet (M : ℝ) v x ⊆ phaseProgressSet (M : ℝ) v y := by
    apply phaseProgressSet_mono
    · intro i hvi hxi
      have hm := hNmono i hvi
      have hy0 := hstep.2.1.2 i
      linarith
    · intro i hvi hxi
      exact (htrap i hvi hxi).2
  obtain ⟨i, hgi, hblocked⟩ := hsat
  have hxi : 0 < x i := by
    by_contra hn
    have hxi0 : x i = 0 := le_antisymm (le_of_not_gt hn) (hx.2 i)
    have hz := hzero i hxi0
    linarith
  have hyi : y i = 0 := hblocked
  have hevent : ∃ i,
      (v i = 0 ∧ x i ≠ 0 ∧ y i = 0) ∨
      (v i ≠ 0 ∧ ¬ x i ≤ (M : ℝ) * v i ∧ y i ≤ (M : ℝ) * v i) := by
    refine ⟨i, ?_⟩
    by_cases hvi : v i = 0
    · exact Or.inl ⟨hvi, ne_of_gt hxi, hyi⟩
    · right
      refine ⟨hvi, ?_, ?_⟩
      · intro htrapped
        have hb := (htrap i hvi htrapped).1
        rw [hyi] at hb
        linarith
      · rw [hyi]
        exact mul_nonneg hMr0 (hv i)
  refine ⟨y, hstep, phaseProgressSet_ssubset_of_event (M : ℝ) v x y hprogress hevent,
    hNmono, ?_⟩
  intro j hj htrapj
  exact (htrap j hj htrapj).1

end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace HirschCircuit

/-- Concrete elimination parameters. No maximum-ratio selector is needed:
any positive target-zero coordinate with small enough reference ratio works.
This is a simplification of our support-safe adaptation, not a sharper source
claim. The output is a genuine maximal circuit step with strict progress. -/
theorem exists_elimination_step_of_small_ratio {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ)
    (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r x : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x)
    (q : Fin n) (hvq : v q = 0) (hxq : 0 < x q) (hrq : 0 < r q)
    (hsmall : x q / r q ≤ 1 / (2 * (M : ℝ) ^ 2)) :
    ∃ y : Fin n → ℝ,
      StandardCircuitStep K v x y ∧
      phaseProgressSet (M : ℝ) v x ⊂ phaseProgressSet (M : ℝ) v y ∧
      (∀ i, v i = 0 → y i ≤ x i) ∧
      ∀ i, v i ≠ 0 → x i ≤ (M : ℝ) * v i → x i / 2 ≤ y i := by
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMrpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMrpos
  let lam : ℝ := 1 / (2 * (M : ℝ))
  let tau : ℝ := 1 / (2 * (M : ℝ) ^ 2)
  let rho : ℝ := x q / r q
  let eta : ℝ := (1 - lam) * rho / (1 - rho)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hlamId : (M : ℝ) * lam = 1 / 2 := by
    dsimp [lam]
    field_simp [hMne] <;> ring
  have hlamLt : lam < 1 := by nlinarith only [hlamId, hlam, hMr]
  have htauLam : tau ≤ lam := by
    dsimp [tau, lam]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hMr]
  have htauId : (M : ℝ) * tau = lam := by
    dsimp [tau, lam]
    field_simp [hMne] <;> ring
  have hrhoPos : 0 < rho := div_pos hxq hrq
  have hrhoTau : rho ≤ tau := hsmall
  have hrhoLam : rho ≤ lam := hrhoTau.trans htauLam
  have hrhoLt : rho < 1 := hrhoLam.trans_lt hlamLt
  obtain ⟨heta, hetaRho⟩ := extrapolation_eta_bounds lam rho
    (le_of_lt hlamLt) (le_of_lt hrhoPos) hrhoLam hrhoLt
  have hetaM : (M : ℝ) * eta ≤ lam := by
    calc
      (M : ℝ) * eta ≤ (M : ℝ) * tau :=
        mul_le_mul_of_nonneg_left (hetaRho.trans hrhoTau) (le_of_lt hMrpos)
      _ = lam := htauId
  have hetaLam : eta ≤ lam := hetaRho.trans hrhoLam
  have hN : ∀ i, v i = 0 →
      lam * (v i - x i) + eta * (x i - r i) ≤ 0 := by
    intro i hvi
    have h1 : 0 ≤ (lam - eta) * x i :=
      mul_nonneg (sub_nonneg.mpr hetaLam) (hx.2 i)
    have h2 : 0 ≤ eta * r i := mul_nonneg heta (hr.2 i)
    rw [hvi]
    nlinarith only [h1, h2]
  have hrhoEq : rho * r q = x q := div_mul_cancel₀ _ (ne_of_gt hrq)
  have hetaEq : eta * (1 - rho) = (1 - lam) * rho :=
    div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hrhoLt))
  have hbalance : eta * (r q - x q) = (1 - lam) * x q := by
    calc
      eta * (r q - x q) = (eta * (1 - rho)) * r q := by rw [← hrhoEq]; ring
      _ = ((1 - lam) * rho) * r q := by rw [hetaEq]
      _ = (1 - lam) * x q := by rw [mul_assoc, hrhoEq]
  have hq : lam * (v q - x q) + eta * (x q - r q) = -x q := by
    rw [hvq]
    nlinarith only [hbalance]
  exact exists_support_safe_elimination_step K M hM hnM v r x hv hr hx heq
    lam eta hlam heta (le_of_eq hlamId) hetaM hN q hxq hq

end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

/-- Extremality supplies a live target-zero coordinate whenever the current
point differs from the target. The corrected phase invariant ensures its
reference denominator is positive. -/
theorem exists_live_target_zero {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℝ) (v r x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x) (hne : x ≠ v) :
    ∃ q, q ∈ liveZeroSet v r ∧ 0 < x q ∧ 0 < r q := by
  classical
  have hex : ∃ q, v q = 0 ∧ x q ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (eq_target_of_zero_off_support K v x hv hx hn)
  obtain ⟨q, hvq, hxq⟩ := hex
  have hrq : r q ≠ 0 := by
    intro hrq0
    exact hxq ((same_phase_zero_iff M v r x heq q hvq).mp hrq0)
  refine ⟨q, ?_, ?_, ?_⟩
  · exact (mem_liveZeroSet v r q).mpr ⟨hvq, hrq⟩
  · exact lt_of_le_of_ne (hx.2 q) (Ne.symm hxq)
  · exact lt_of_le_of_ne (hr.2 q) (Ne.symm hrq)

theorem ratio_le_phasePotential {n : ℕ}
    (v r x : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (hx : ∀ i, 0 ≤ x i)
    (q : Fin n) (hq : q ∈ liveZeroSet v r) :
    x q / r q ≤ phasePotential v r x := by
  exact Finset.single_le_sum (fun i _ => div_nonneg (hx i) (hr i)) hq

theorem phasePotential_pos_of_ne_target {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℝ) (v r x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x) (hne : x ≠ v) :
    0 < phasePotential v r x := by
  obtain ⟨q, hq, hxq, hrq⟩ := exists_live_target_zero K M v r x hv hr hx heq hne
  exact (div_pos hxq hrq).trans_le (ratio_le_phasePotential v r x hr.2 hx.2 q hq)

/-- Resetting the reference makes every live ratio exactly one. -/
theorem phasePotential_self_le_n {n : ℕ} (v r : Fin n → ℝ) :
    phasePotential v r r ≤ (n : ℝ) := by
  classical
  have hid : phasePotential v r r = ((liveZeroSet v r).card : ℝ) := by
    unfold phasePotential
    calc
      (∑ i ∈ liveZeroSet v r, r i / r i) = ∑ _i ∈ liveZeroSet v r, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact div_self ((mem_liveZeroSet v r i).mp hi).2
      _ = ((liveZeroSet v r).card : ℝ) := by simp
  rw [hid]
  have hcard : (liveZeroSet v r).card ≤ n := by
    simpa using (Finset.card_le_card (Finset.subset_univ (liveZeroSet v r)))
  exact_mod_cast hcard

/-- A small potential supplies all concrete elimination hypotheses; no
unproved progress or maximal-step assumption is passed in. -/
theorem exists_elimination_step_of_small_potential {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x)
    (hne : x ≠ v) (hsmall : phasePotential v r x ≤ 1 / (2 * (M : ℝ) ^ 2)) :
    ∃ y : Fin n → ℝ, StandardCircuitStep K v x y ∧
      phaseProgressSet (M : ℝ) v x ⊂ phaseProgressSet (M : ℝ) v y := by
  obtain ⟨q, hq, hxq, hrq⟩ := exists_live_target_zero K (M : ℝ) v r x hv hr hx heq hne
  have hvq := ((mem_liveZeroSet v r q).mp hq).1
  have hratio := (ratio_le_phasePotential v r x hr.2 hx.2 q hq).trans hsmall
  obtain ⟨y, hstep, hstrict, _⟩ := exists_elimination_step_of_small_ratio
    K M hM hnM v r x hv.1.2 hr hx heq q hvq hxq hrq hratio
  exact ⟨y, hstep, hstrict⟩

end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

theorem standardCircuitWalk_stationary {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c) (L : ℕ) :
    StandardCircuitWalk K c L v v := by
  exact ⟨fun _ => v, rfl, rfl, fun _ _ => hv, fun _ _ => Or.inl rfl⟩

/-- Concatenate padded walks, using the common endpoint at the junction. -/
theorem standardCircuitWalk_trans {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L M : ℕ} {u v z : Fin n → ℝ}
    (h₁ : StandardCircuitWalk K c L u v)
    (h₂ : StandardCircuitWalk K c M v z) :
    StandardCircuitWalk K c (L + M) u z := by
  obtain ⟨w₁, h10, h1L, hf₁, hs₁⟩ := h₁
  obtain ⟨w₂, h20, h2M, hf₂, hs₂⟩ := h₂
  let w : ℕ → (Fin n → ℝ) := fun j =>
    if j < L then w₁ j else w₂ (j - L)
  have hfirst : ∀ j, j ≤ L → w j = w₁ j := by
    intro j hj
    by_cases hjlt : j < L
    · simp only [w, if_pos hjlt]
    · have hjEq : j = L := by omega
      subst j
      simp [w, h20, h1L]
  have hsecond : ∀ j, L ≤ j → w j = w₂ (j - L) := by
    intro j hj
    simp only [w, if_neg (not_lt_of_ge hj)]
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · rw [hfirst 0 (Nat.zero_le _), h10]
  · rw [hsecond (L + M) (by omega), Nat.add_sub_cancel_left, h2M]
  · intro j hj
    by_cases hjL : j ≤ L
    · rw [hfirst j hjL]
      exact hf₁ j hjL
    · rw [hsecond j (by omega)]
      exact hf₂ (j - L) (by omega)
  · intro j hj
    by_cases hjL : j < L
    · rw [hfirst j (by omega), hfirst (j + 1) (by omega)]
      exact hs₁ j hjL
    · have hjge : L ≤ j := by omega
      rw [hsecond j hjge, hsecond (j + 1) (by omega)]
      have hidx : j + 1 - L = (j - L) + 1 := by omega
      rw [hidx]
      exact hs₂ (j - L) (by omega)

theorem standardCircuitWalk_mono {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L M : ℕ} {u v : Fin n → ℝ}
    (h : StandardCircuitWalk K c L u v) (hLM : L ≤ M) :
    StandardCircuitWalk K c M u v := by
  have hv : v ∈ StandardSlice K c := by
    obtain ⟨w, _, hwL, hf, _⟩ := h
    simpa only [hwL] using hf L (le_rfl)
  have hstay := standardCircuitWalk_stationary K c v hv (M - L)
  have hcat := standardCircuitWalk_trans K c h hstay
  simpa only [Nat.add_sub_of_le hLM] using hcat

theorem standardCircuitWalk_of_step {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x y : Fin n → ℝ)
    (h : StandardCircuitStep K c x y) :
    StandardCircuitWalk K c 1 x y := by
  let w : ℕ → (Fin n → ℝ) := fun j => if j = 0 then x else y
  refine ⟨w, by simp [w], by simp [w], ?_, ?_⟩
  · intro j hj
    interval_cases j <;> simp [w, h.1, h.2.1]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    right
    simpa only [w, if_pos rfl, Nat.zero_add, if_neg (by decide : ¬(1 : ℕ) = 0)] using h

end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

/-- One block of `M` multiplicative contractions by `1-1/M` loses at least a
factor two. This is a rational Bernoulli/binomial estimate, not a logarithmic
argument. -/
theorem contraction_block_half (M : ℕ) (hM : 2 ≤ M) :
    ((1 - 1 / (M : ℝ)) ^ M) ≤ (1 / 2 : ℝ) := by
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  let q : ℝ := 1 - 1 / (M : ℝ)
  let p : ℝ := 1 + 1 / (M : ℝ)
  have hinv0 : 0 ≤ 1 / (M : ℝ) := le_of_lt (one_div_pos.mpr hMpos)
  have hinv1 : 1 / (M : ℝ) ≤ 1 := by
    exact (div_le_one hMpos).2 (by linarith)
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp2 : (2 : ℝ) ≤ p ^ M := by
    have hbern := one_add_mul_le_pow (a := 1 / (M : ℝ)) (by linarith) M
    have hcast : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp [hMne]
    dsimp [p]
    rw [hcast] at hbern
    norm_num at hbern ⊢
    exact hbern
  have hqp0 : 0 ≤ q * p := mul_nonneg hq0 hp0
  have hqp1 : q * p ≤ 1 := by
    dsimp [q, p]
    have hs : 0 ≤ (1 / (M : ℝ)) ^ 2 := sq_nonneg _
    nlinarith
  have hpow : (q * p) ^ M ≤ (1 : ℝ) ^ M :=
    pow_le_pow_left₀ hqp0 hqp1 M
  rw [mul_pow, one_pow] at hpow
  have hqpow0 : 0 ≤ q ^ M := pow_nonneg hq0 _
  have hmul : 2 * q ^ M ≤ q ^ M * p ^ M := by
    simpa [mul_comm] using (mul_le_mul_of_nonneg_left hp2 hqpow0)
  have hqhalf : q ^ M ≤ (1 / 2 : ℝ) := by
    nlinarith only [hmul, hpow]
  simpa [q] using hqhalf

/-- A purely natural-number exponential envelope used after taking `4*M`
contraction blocks. -/
theorem two_mul_cube_le_two_pow_four_mul (M : ℕ) (hM : 1 ≤ M) :
    2 * M ^ 3 ≤ 2 ^ (4 * M) := by
  have hsqp1 := Nat.two_mul_sq_add_one_le_two_pow_two_mul M
  have hsq : 2 * M ^ 2 ≤ 2 ^ (2 * M) := by omega
  have hMle : M ≤ 2 * M ^ 2 := by nlinarith
  have hMpow : M ≤ 2 ^ (2 * M) := hMle.trans hsq
  have hmul := Nat.mul_le_mul hsq hMpow
  calc
    2 * M ^ 3 = (2 * M ^ 2) * M := by ring
    _ ≤ (2 ^ (2 * M)) * (2 ^ (2 * M)) := hmul
    _ = 2 ^ (4 * M) := by rw [← pow_add]; congr 1 <;> ring

/-- After `4*M^2` norm contractions, an initial potential at most `M` is at
most `1/(2*M^2)`, the elimination threshold used by the support-safe proof. -/
theorem contraction_to_elimination_threshold (M : ℕ) (hM : 2 ≤ M) :
    (M : ℝ) * (1 - 1 / (M : ℝ)) ^ (4 * M ^ 2) ≤
      1 / (2 * (M : ℝ) ^ 2) := by
  have hblock := contraction_block_half M hM
  have hM1 : 1 ≤ M := by omega
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hq0 : 0 ≤ (1 - 1 / (M : ℝ)) := by
    have hinv1 : 1 / (M : ℝ) ≤ 1 := (div_le_one hMr).2 (by exact_mod_cast hM1)
    linarith
  have hpow0 : 0 ≤ (1 - 1 / (M : ℝ)) ^ M := pow_nonneg hq0 _
  have hpow :
      ((1 - 1 / (M : ℝ)) ^ M) ^ (4 * M) ≤
        ((1 / 2 : ℝ)) ^ (4 * M) :=
    pow_le_pow_left₀ hpow0 hblock (4 * M)
  have hexp : M * (4 * M) = 4 * M ^ 2 := by ring
  rw [← pow_mul, hexp] at hpow
  have hnat := two_mul_cube_le_two_pow_four_mul M hM1
  have hnatR : (2 : ℝ) * (M : ℝ) ^ 3 ≤ (2 : ℝ) ^ (4 * M) := by
    exact_mod_cast hnat
  have htwo : (0 : ℝ) < (2 : ℝ) ^ (4 * M) := pow_pos (by norm_num) _
  have hden : (0 : ℝ) < 2 * (M : ℝ) ^ 2 := by positivity
  have hfrac' : (M : ℝ) / (2 : ℝ) ^ (4 * M) ≤
      1 / (2 * (M : ℝ) ^ 2) := by
    apply (div_le_div_iff₀ htwo hden).2
    nlinarith only [hnatR]
  have hfrac : (M : ℝ) * (1 / 2 : ℝ) ^ (4 * M) ≤
      1 / (2 * (M : ℝ) ^ 2) := by
    rw [one_div_pow]
    simpa [div_eq_mul_inv] using hfrac'
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hfrac


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace HirschCircuit

/-- Recenter the affine nonnegative slice at any feasible point. -/
theorem standardSlice_recenter {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c) :
    StandardSlice K c = StandardSlice K v := by
  ext s
  constructor
  · intro hs
    refine ⟨?_, hs.2⟩
    have hdecomp : s - v = (s - c) - (v - c) := by
      funext i
      simp only [Pi.sub_apply]
      ring
    rw [hdecomp]
    exact K.sub_mem hs.1 hv.1
  · intro hs
    refine ⟨?_, hs.2⟩
    have hdecomp : s - c = (s - v) + (v - c) := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [hdecomp]
    exact K.add_mem hs.1 hv.1

/-- `StandardCircuitStep` depends on the affine center only through the
underlying slice, so recentering at a feasible target preserves it exactly. -/
theorem standardCircuitStep_recenter_iff {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v x y : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c) :
    StandardCircuitStep K c x y ↔ StandardCircuitStep K v x y := by
  have hset := standardSlice_recenter K c v hv
  simp only [StandardCircuitStep]
  rw [hset]

/-- Padded standard-form circuit walks are unchanged by recentering the affine
slice at a feasible point. -/
theorem standardCircuitWalk_recenter_iff {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c)
    (L : ℕ) (u w : Fin n → ℝ) :
    StandardCircuitWalk K c L u w ↔ StandardCircuitWalk K v L u w := by
  have hset := standardSlice_recenter K c v hv
  simp only [StandardCircuitWalk, StandardCircuitStep]
  rw [hset]

/-- Extreme points transfer verbatim under recentering because the feasible
sets are literally equal. -/
theorem extremePoint_recenter {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v x : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c)
    (hx : x ∈ Set.extremePoints ℝ (StandardSlice K c)) :
    x ∈ Set.extremePoints ℝ (StandardSlice K v) := by
  rwa [← standardSlice_recenter K c v hv]


end HirschCircuit


set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace HirschCircuit

private theorem walk_end_mem {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L : ℕ} {u x : Fin n → ℝ} (h : StandardCircuitWalk K c L u x) :
    x ∈ StandardSlice K c := by
  obtain ⟨w, _, hwL, hf, _⟩ := h
  simpa only [hwL] using hf L (le_rfl)

/-- Run norm steps only while the fixed-reference phase has not ended.
After an event or arrival, pad at that endpoint. Otherwise the potential
contracts geometrically and the reference/current progress sets stay equal. -/
theorem norm_steps_or_phase_progress {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (k : ℕ) :
    ∃ x : Fin n → ℝ, StandardCircuitWalk K v k r x ∧
      (x = v ∨ phaseProgressSet (M : ℝ) v r ⊂ phaseProgressSet (M : ℝ) v x ∨
        (phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x ∧
          phasePotential v r x ≤ (1 - 1 / (M : ℝ)) ^ k * phasePotential v r r)) := by
  have hMpos : 0 < M := by omega
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMrpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hq0 : 0 ≤ 1 - 1 / (M : ℝ) := by
    have hdiv : 1 / (M : ℝ) ≤ 1 := (div_le_one hMrpos).mpr (by linarith)
    linarith
  induction k with
  | zero =>
      refine ⟨r, standardCircuitWalk_stationary K v r hr 0, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      simp
  | succ k ih =>
      obtain ⟨x, hwalk, hstate⟩ := ih
      rcases hstate with htarget | hstrict | ⟨heq, hbound⟩
      · exact ⟨x, standardCircuitWalk_mono K v hwalk (Nat.le_succ k), Or.inl htarget⟩
      · exact ⟨x, standardCircuitWalk_mono K v hwalk (Nat.le_succ k), Or.inr (Or.inl hstrict)⟩
      · by_cases hxv : x = v
        · exact ⟨x, standardCircuitWalk_mono K v hwalk (Nat.le_succ k), Or.inl hxv⟩
        · have hx := walk_end_mem K v hwalk
          have hW := phasePotential_pos_of_ne_target K (M : ℝ) v r x hv hr hx heq hxv
          obtain ⟨y, g, alpha, ha, ha1, haM, hstep, hyform, hWy, hcontract, hmono, hN⟩ :=
            exists_norm_reduction_step K M hMpos hnM v r x hv.1.2 hr.2 hx hW
          have hcat : StandardCircuitWalk K v (k + 1) r y :=
            standardCircuitWalk_trans K v hwalk (standardCircuitWalk_of_step K v x y hstep)
          have hmono' : phaseProgressSet (M : ℝ) v r ⊆ phaseProgressSet (M : ℝ) v y := by
            rw [heq]
            exact hmono
          refine ⟨y, hcat, Or.inr ?_⟩
          by_cases heq' : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v y
          · right
            refine ⟨heq', ?_⟩
            calc
              phasePotential v r y ≤ (1 - 1 / (M : ℝ)) * phasePotential v r x := hcontract
              _ ≤ (1 - 1 / (M : ℝ)) *
                  ((1 - 1 / (M : ℝ)) ^ k * phasePotential v r r) :=
                mul_le_mul_of_nonneg_left hbound hq0
              _ = (1 - 1 / (M : ℝ)) ^ (k + 1) * phasePotential v r r := by
                rw [pow_succ]
                ring
          · exact Or.inl (ssubset_of_ne_of_subset heq' hmono')

/-- Every phase reaches the target or strictly enlarges the finite progress
set in at most `4*M^2+1` actual/padded steps. Reference resets are permitted
only after this conclusion, so lost target-zero support is never forgotten. -/
theorem exists_bounded_progress_phase {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) :
    ∃ y : Fin n → ℝ, StandardCircuitWalk K v (4 * M ^ 2 + 1) r y ∧
      (y = v ∨ phaseProgressSet (M : ℝ) v r ⊂ phaseProgressSet (M : ℝ) v y) := by
  obtain ⟨x, hwalk, hstate⟩ := norm_steps_or_phase_progress K M hM hnM v r hv hr (4 * M ^ 2)
  rcases hstate with htarget | hstrict | ⟨heq, hbound⟩
  · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inl htarget⟩
  · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inr hstrict⟩
  · by_cases hxv : x = v
    · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inl hxv⟩
    · have hx := walk_end_mem K v hwalk
      have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hMrpos : (0 : ℝ) < (M : ℝ) := by linarith
      have hq0 : 0 ≤ 1 - 1 / (M : ℝ) := by
        have hdiv : 1 / (M : ℝ) ≤ 1 := (div_le_one hMrpos).mpr (by linarith)
        linarith
      have hstart : phasePotential v r r ≤ (M : ℝ) :=
        (phasePotential_self_le_n v r).trans (by exact_mod_cast hnM)
      have hsmall : phasePotential v r x ≤ 1 / (2 * (M : ℝ) ^ 2) := by
        calc
          phasePotential v r x ≤ (1 - 1 / (M : ℝ)) ^ (4 * M ^ 2) * phasePotential v r r := hbound
          _ ≤ (1 - 1 / (M : ℝ)) ^ (4 * M ^ 2) * (M : ℝ) :=
            mul_le_mul_of_nonneg_left hstart (pow_nonneg hq0 _)
          _ = (M : ℝ) * (1 - 1 / (M : ℝ)) ^ (4 * M ^ 2) := mul_comm _ _
          _ ≤ 1 / (2 * (M : ℝ) ^ 2) := contraction_to_elimination_threshold M hM
      obtain ⟨y, hstep, hstrict⟩ := exists_elimination_step_of_small_potential
        K M hM hnM v r x hv hr hx heq hxv hsmall
      refine ⟨y, standardCircuitWalk_trans K v hwalk
        (standardCircuitWalk_of_step K v x y hstep), Or.inr ?_⟩
      rw [heq]
      exact hstrict

/-- Induction on the remaining progress budget assembles all phases. -/
theorem standardCircuitWalk_phase_budget {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (hM : 2 ≤ M) (hnM : n ≤ M)
    (v : Fin n → ℝ) (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v)) :
    ∀ k : ℕ, ∀ r ∈ StandardSlice K v,
      n ≤ (phaseProgressSet (M : ℝ) v r).card + k →
      StandardCircuitWalk K v (k * (4 * M ^ 2 + 1)) r v := by
  intro k
  induction k with
  | zero =>
      intro r hr hk
      have hfull : phaseProgressSet (M : ℝ) v r = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_zero] using hk
      have hrv := eq_target_of_full_phase_progress K (M : ℝ) v r hv hr hfull
      subst r
      exact standardCircuitWalk_stationary K v v hv.1 _
  | succ k ih =>
      intro r hr hk
      obtain ⟨y, hwalk, hy⟩ := exists_bounded_progress_phase K M hM hnM v r hv hr
      rcases hy with htarget | hstrict
      · rw [htarget] at hwalk
        apply standardCircuitWalk_mono K v hwalk
        nlinarith
      · have hcard := Finset.card_lt_card hstrict
        have hbudget : n ≤ (phaseProgressSet (M : ℝ) v y).card + k := by omega
        have htail := ih y (walk_end_mem K v hwalk) hbudget
        have hcat := standardCircuitWalk_trans K v hwalk htail
        have hid : (4 * M ^ 2 + 1) + k * (4 * M ^ 2 + 1) =
            (k + 1) * (4 * M ^ 2 + 1) := by ring
        simpa only [hid] using hcat

/-- Matrix-free cubic routing from any feasible point to an extreme target.
No boundedness, basis-extension or source-theorem hypothesis is used. -/
theorem standardCircuitWalk_cubic_centered {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (v r : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) :
    StandardCircuitWalk K v (17 * n ^ 3) r v := by
  by_cases hn0 : n = 0
  · subst n
    have hrv : r = v := by funext i; exact Fin.elim0 i
    subst r
    exact standardCircuitWalk_stationary K v v hv.1 _
  · have hn : 1 ≤ n := by omega
    let M : ℕ := max 2 n
    have hM : 2 ≤ M := le_max_left _ _
    have hnM : n ≤ M := le_max_right _ _
    have hMupper : M ≤ 2 * n := max_le (by omega) (by omega)
    have hwalk := standardCircuitWalk_phase_budget K M hM hnM v hv n r hr (by omega)
    exact standardCircuitWalk_mono K v hwalk (event_budget_le_cubic n M hn hMupper)

/-- Recenter at the target without changing the circuit directions or steps. -/
theorem standardCircuitWalk_cubic {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c r v : Fin n → ℝ)
    (hr : r ∈ StandardSlice K c)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K c)) :
    StandardCircuitWalk K c (17 * n ^ 3) r v := by
  have hset := standardSlice_recenter K c v hv.1
  have hv' : v ∈ Set.extremePoints ℝ (StandardSlice K v) := by rwa [← hset]
  have hr' : r ∈ StandardSlice K v := by rwa [← hset]
  exact (standardCircuitWalk_recenter_iff K c v hv.1 (17 * n ^ 3) r v).mpr
    (standardCircuitWalk_cubic_centered K v r hv' hr')

/-- Discharge the formerly conditional source interface constructively. -/
theorem standard_cubic_circuit_bound : StandardCubicCircuitBound := by
  refine ⟨17, ?_⟩
  intro n K c u hu v hv
  exact standardCircuitWalk_cubic K c u v hu.1 hv

end HirschCircuit

open scoped RealInnerProductSpace
theorem solution :
∃ C : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
        Hirsch.Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hirsch.Hpoly a b ∧
        Hirsch.RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) ∧
        Hirsch.StrictlyFeasibleRows (fun j => a (e j)) (fun j => b (e j)) ∧
        Hirsch.RowCircuitWalk (fun j => a (e j)) (fun j => b (e j))
          (C * (m + d) ^ 3) u v := by
  exact HirschCircuit.cubic_circuit_walk_bound_of_standard HirschCircuit.standard_cubic_circuit_bound
#print axioms solution
