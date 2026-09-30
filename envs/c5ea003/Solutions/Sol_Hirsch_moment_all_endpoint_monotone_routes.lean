-- Prove2me | solution 1 for Hirsch.moment_all_endpoint_monotone_routes
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-18T16:26:42.651557+00:00
-- url     : https://prove2.me/submissions/550fd8a6-18bc-4b1d-80ed-9e2f3fc1170e

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

/-! Exact accepted evaluation helpers from #285/#286 via #287. -/
namespace Hirsch.MomentSmallFaces

/-- The constant coefficient is separated before centering the moment rows. -/
lemma eval_split (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n) (t : ℝ) :
    p.eval t = p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) * t ^ (j.val + 1) := by
  calc
    p.eval t = ∑ j ∈ Finset.range (n + 1), p.coeff j * t ^ j :=
      Polynomial.eval_eq_sum_range' (by omega) t
    _ = ∑ j : Fin (n + 1), p.coeff j.val * t ^ j.val := Finset.sum_range _
    _ = p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) * t ^ (j.val + 1) := by
      simpa using (Fin.sum_univ_succ
        (fun j : Fin (n + 1) => p.coeff j.val * t ^ j.val))

/-- Averaging evaluations is the same as evaluating the coefficient functional
on the averaged moment vector. No extremal-point or support oracle is used. -/
lemma average_split {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (hm : (Fintype.card ι : ℝ) ≠ 0) :
    (∑ i, p.eval (a i)) / (Fintype.card ι : ℝ) =
      p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) *
        ((∑ i, a i ^ (j.val + 1)) / (Fintype.card ι : ℝ)) := by
  classical
  have hexpand : (∑ i, p.eval (a i)) =
      (Fintype.card ι : ℝ) * p.coeff 0 +
        ∑ j : Fin n, p.coeff (j.val + 1) * (∑ i, a i ^ (j.val + 1)) := by
    simp_rw [eval_split p n hp]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact (Finset.mul_sum _ _ _).symm
  rw [hexpand, add_div, Finset.sum_div]
  congr 1
  · field_simp [hm]
  · apply Finset.sum_congr rfl
    intro j _
    ring

lemma centered_eval {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (hm : (Fintype.card ι : ℝ) ≠ 0) (i : ι) :
    (∑ j : Fin n,
      (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) *
        p.coeff (j.val + 1)) =
      p.eval (a i) - (∑ l, p.eval (a l)) / (Fintype.card ι : ℝ) := by
  classical
  have he := eval_split p n hp (a i)
  have hav := average_split a p n hp hm
  calc
    (∑ j : Fin n,
      (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) *
        p.coeff (j.val + 1)) =
      (∑ j : Fin n, p.coeff (j.val + 1) * a i ^ (j.val + 1)) -
      ∑ j : Fin n, p.coeff (j.val + 1) *
        ((∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = p.eval (a i) - (∑ l, p.eval (a l)) / (Fintype.card ι : ℝ) := by
      linarith

end Hirsch.MomentSmallFaces

namespace Hirsch.MomentBarycentric

noncomputable def row {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) : ℝ :=
  ∑ j : Fin d,
    (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (m : ℝ)) * x j

noncomputable def slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) : Polynomial ℝ :=
  1 - ∑ j : Fin d,
    (Polynomial.X ^ (j.val + 1) -
      Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))) * Polynomial.C (x j)

lemma eval_slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) :
    (slack a x).eval (a i) = 1 - row a x i := by
  simp [slack, row, Polynomial.eval_finsetSum]

lemma degree_slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) :
    (slack a x).natDegree ≤ d := by
  unfold slack
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  calc
    ((Polynomial.X ^ (j.val + 1) -
        Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))) *
        Polynomial.C (x j)).natDegree ≤
        (Polynomial.X ^ (j.val + 1) -
          Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree +
          (Polynomial.C (x j)).natDegree := Polynomial.natDegree_mul_le
    _ = (Polynomial.X ^ (j.val + 1) -
          Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree := by simp
    _ ≤ max (Polynomial.X ^ (j.val + 1) : Polynomial ℝ).natDegree
          (Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ = j.val + 1 := by simp
    _ ≤ d := by omega

lemma sum_row_zero {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hm : (m : ℝ) ≠ 0) : ∑ i, row a x i = 0 := by
  unfold row
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  have hc : (∑ _i : Fin m, (∑ l : Fin m, a l ^ (j.val + 1)) / (m : ℝ)) =
      ∑ l : Fin m, a l ^ (j.val + 1) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hm]
    <;> ring
  rw [hc, sub_self, zero_mul]

lemma slack_ne_zero {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hm : (m : ℝ) ≠ 0) : slack a x ≠ 0 := by
  intro hz
  have hsum : (∑ i : Fin m, (slack a x).eval (a i)) = (m : ℝ) := by
    simp_rw [eval_slack]
    rw [Finset.sum_sub_distrib, sum_row_zero a x hm]
    simp
  have hzero : (∑ i : Fin m, (slack a x).eval (a i)) = 0 := by simp [hz]
  exact hm (hsum.symm.trans hzero)


end Hirsch.MomentBarycentric

namespace Hirsch.MomentVertices

open Set MomentBarycentric

/-- Exact finite-margin helper reused from accepted #290. -/
lemma finite_margin {ι : Type*} (S : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i ∈ S, e * |t i| < a i := by
  classical
  revert ha
  induction S using Finset.induction_on with
  | empty =>
      intro ha
      exact ⟨1, by norm_num, by simp⟩
  | @insert i S hi ih =>
      intro ha
      obtain ⟨e, he, hS⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai : 0 < a i := ha i (Finset.mem_insert_self i S)
      have hd : 0 < |t i| + 1 := by positivity
      let f : ℝ := a i / (|t i| + 1)
      have hf : 0 < f := div_pos hai hd
      have hfeq : f * (|t i| + 1) = a i := by
        dsimp [f]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      refine ⟨min e f, lt_min he hf, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have hb := mul_le_mul_of_nonneg_right (min_le_right e f) (abs_nonneg (t i))
        nlinarith
      · exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (min_le_left e f) (abs_nonneg (t j))) (hS j hj)

lemma row_add {d m : ℕ} (a : Fin m → ℝ) (x y : Fin d → ℝ) (i : Fin m) :
    row a (x+y) i = row a x i + row a y i := by
  simp only [row, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma row_sub {d m : ℕ} (a : Fin m → ℝ) (x y : Fin d → ℝ) (i : Fin m) :
    row a (x-y) i = row a x i - row a y i := by
  simp only [row, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma row_smul {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (c : ℝ) (i : Fin m) :
    row a (c • x) i = c * row a x i := by
  unfold row
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

noncomputable def active {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => row a x i = 1)

lemma mem_active {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) :
    i ∈ active a x ↔ row a x i = 1 := by
  simp [active]

noncomputable def activeEval {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] ((active a x) → ℝ) where
  toFun z i := row a z i.val
  map_add' y z := by
    funext i
    exact row_add a y z i.val
  map_smul' c z := by
    funext i
    exact row_smul a z c i.val

/-- Root counting applies even to infeasible ambient points. -/
theorem tight_card_le {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ) :
    (active a x).card ≤ d := by
  classical
  by_contra hn
  have hlt : d < (active a x).card := lt_of_not_ge hn
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  apply slack_ne_zero a x hm0
  have hnat : (slack a x).natDegree < (active a x).card :=
    (degree_slack a x).trans_lt hlt
  have hdeg : (slack a x).degree < ((active a x).card : WithBot ℕ) :=
    lt_of_le_of_lt (slack a x).degree_le_natDegree (by exact_mod_cast hnat)
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (active a x) ha.injOn hdeg
  intro i hi
  rw [eval_slack, (mem_active a x i).mp hi]
  ring

/-- Interpolation and a centering correction construct arbitrary active-row
values. Full rank is a conclusion, not a supplied inverse or independence. -/
theorem activeEval_surjective {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ) :
    Function.Surjective (activeEval a x) := by
  classical
  intro values
  let I := ↥(active a x)
  let b : I → ℝ := fun i => a i.val
  have hb : Function.Injective b := by
    intro i j hij
    apply Subtype.ext
    exact ha hij
  let p : Polynomial ℝ := Lagrange.interpolate Finset.univ b values
  have hnat : p.natDegree ≤ Fintype.card I - 1 := by
    apply Polynomial.natDegree_le_iff_degree_le.mpr
    simpa only [Finset.card_univ] using Lagrange.degree_interpolate_le (s := Finset.univ) (v := b) values hb.injOn
  have hcard : Fintype.card I ≤ d := by
    simpa only [I, Fintype.card_coe] using tight_card_le a ha hm x
  have hp : p.natDegree ≤ d := by omega
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hfin0 : (Fintype.card (Fin m) : ℝ) ≠ 0 := by
    simpa only [Fintype.card_fin] using hm0
  let y : Fin d → ℝ := fun j => p.coeff (j.val+1)
  let c : ℝ := (∑ i : Fin m, p.eval (a i)) / (m : ℝ)
  have he : ∀ i : Fin m, row a y i = p.eval (a i)-c := by
    intro i
    simpa only [row, y, c, Fintype.card_fin] using
      MomentSmallFaces.centered_eval a p d hp hfin0 i
  refine ⟨y + c • x, ?_⟩
  funext i
  change row a (y + c • x) i.val = values i
  have hix : row a x i.val = 1 := (mem_active a x i.val).mp i.property
  have hev : p.eval (a i.val) = values i :=
    Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := b) values hb.injOn (Finset.mem_univ i)
  rw [row_add, row_smul, hix, he, hev]
  ring

/-- The finite-margin argument detects every nonzero active-kernel motion at
an actual extreme point of the original halfspace intersection. -/
lemma extreme_kernel {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hx : x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ)
    (z : Fin d → ℝ) (hz : ∀ i, row a x i = 1 → row a z i = 0) : z = 0 := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun i => row a x i ≠ 1)
  have hslack : ∀ i ∈ S, 0 < 1-row a x i := by
    intro i hi
    exact sub_pos.mpr (lt_of_le_of_ne (hx.1 i) (Finset.mem_filter.mp hi).2)
  obtain ⟨e,he,hsmall⟩ := finite_margin S (fun i => 1-row a x i)
    (fun i => row a z i) hslack
  have hcuts : ∀ i, row a (x+e•z) i ≤ 1 ∧ row a (x-e•z) i ≤ 1 := by
    intro i
    by_cases hi : row a x i = 1
    · simp only [row_add, row_sub, row_smul, hz i hi, mul_zero, add_zero, sub_zero]
      exact ⟨hx.1 i,hx.1 i⟩
    · have hs : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
      have hb := hsmall i hs
      have hlo := mul_le_mul_of_nonneg_left (neg_abs_le (row a z i)) he.le
      have hhi := mul_le_mul_of_nonneg_left (le_abs_self (row a z i)) he.le
      simp only [row_add, row_sub, row_smul]
      constructor <;> nlinarith
  have hmid : x ∈ openSegment ℝ (x+e•z) (x-e•z) := by
    refine ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have heq : x+e•z=x := hx.2 (fun i => (hcuts i).1) (fun i => (hcuts i).2) hmid
  funext j
  have h := congrFun heq j
  change x j+e*z j=x j at h
  have hprod : e*z j=0 := by linarith
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt he)

lemma extreme_activeEval_injective {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hx : x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ) :
    Function.Injective (activeEval a x) := by
  classical
  intro y z heq
  apply sub_eq_zero.mp
  apply extreme_kernel a x hx (y-z)
  intro i hi
  let j : active a x := ⟨i,(mem_active a x i).mpr hi⟩
  have he : row a y i = row a z i := congrFun heq j
  rw [row_sub, he, sub_self]

lemma extreme_of_activeEval_injective {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hx : ∀ i, row a x i ≤ 1) (hinj : Function.Injective (activeEval a x)) :
    x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ := by
  classical
  refine ⟨hx,?_⟩
  intro y hy z hz hseg
  obtain ⟨u,v,hu,hv,huv,heq⟩ := hseg
  apply hinj
  funext i
  change row a y i.val = row a x i.val
  have hix : row a x i.val = 1 := (mem_active a x i.val).mp i.property
  have hrow := congrArg (fun w : Fin d → ℝ => row a w i.val) heq
  change row a (u • y + v • z) i.val = row a x i.val at hrow
  rw [row_add, row_smul, row_smul, hix] at hrow
  have h1 := mul_nonneg hu.le (sub_nonneg.mpr (hy i.val))
  have h2 := mul_nonneg hv.le (sub_nonneg.mpr (hz i.val))
  have he : u*(1-row a y i.val)=0 := by nlinarith
  have hh : 1-row a y i.val=0 := (mul_eq_zero.mp he).resolve_left (ne_of_gt hu)
  rw [hix]
  linarith

/-- Exactly dimension many tight original rows characterize all actual vertices. -/
theorem extreme_iff_tight_card {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ) :
    x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ ↔
      (∀ i, row a x i ≤ 1) ∧ (active a x).card = d := by
  classical
  constructor
  · intro hx
    refine ⟨hx.1, le_antisymm (tight_card_le a ha hm x) ?_⟩
    have h := LinearMap.finrank_le_finrank_of_injective (extreme_activeEval_injective a x hx)
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      Fintype.card_coe] using h
  · rintro ⟨hx,hcard⟩
    apply extreme_of_activeEval_injective a x hx
    have hdim : Module.finrank ℝ (Fin d → ℝ) =
        Module.finrank ℝ ((active a x) → ℝ) := by
      simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
        Fintype.card_coe, hcard]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
      (activeEval_surjective a ha hm x)

end Hirsch.MomentVertices

namespace Hirsch.MomentEdges

open Set MomentBarycentric MomentVertices

/-- One fewer common label means every source-private row is the same row. -/
lemma common_is_erase {ι : Type*} [DecidableEq ι]
    (I J : Finset ι) (hc : (I ∩ J).card + 1 = I.card) :
    ∃ r, r ∈ I ∧ r ∉ J ∧ I ∩ J = I.erase r := by
  classical
  obtain ⟨r, hrI, hrJ⟩ : ∃ r, r ∈ I ∧ r ∉ J := by
    by_contra hn
    push_neg at hn
    have hsub : I ⊆ J := hn
    have heq : I ∩ J = I := Finset.inter_eq_left.mpr hsub
    rw [heq] at hc
    omega
  refine ⟨r, hrI, hrJ, ?_⟩
  have hsub : I ∩ J ⊆ I.erase r := by
    intro i hi
    have h := Finset.mem_inter.mp hi
    refine Finset.mem_erase.mpr ⟨?_, h.1⟩
    intro heq
    subst i
    exact hrJ h.2
  apply Finset.eq_of_subset_of_card_le hsub
  have he := Finset.card_erase_add_one hrI
  omega

/-- The complete common-row face is a closed original segment. The active
kernel is proved trivial by the accepted vertex criterion, not assumed. -/
theorem common_slice_eq_segment {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (u v : Fin d → ℝ)
    (hu : ∀ i, row a u i ≤ 1) (hv : ∀ i, row a v i ≤ 1)
    (huc : (active a u).card = d) (hvc : (active a v).card = d)
    (hc : (active a u ∩ active a v).card + 1 = d) :
    {z : Fin d → ℝ | (∀ i, row a z i ≤ 1) ∧
      ∀ i ∈ active a u ∩ active a v, row a z i = 1} = segment ℝ u v := by
  classical
  have hue : u ∈ ({z : Fin d → ℝ | ∀ i, row a z i ≤ 1}).extremePoints ℝ :=
    (extreme_iff_tight_card a ha hm u).mpr ⟨hu, huc⟩
  have hinj := extreme_activeEval_injective a u hue
  obtain ⟨r, hru, hrv, her⟩ := common_is_erase (active a u) (active a v) (by omega)
  have hcr : (active a v ∩ active a u).card + 1 = (active a v).card := by
    rw [Finset.inter_comm]
    omega
  obtain ⟨q, hqv, hqu, _⟩ := common_is_erase (active a v) (active a u) hcr
  have hru1 : row a u r = 1 := (mem_active a u r).mp hru
  have hrvlt : row a v r < 1 :=
    lt_of_le_of_ne (hv r) (fun h => hrv ((mem_active a v r).mpr h))
  have hqv1 : row a v q = 1 := (mem_active a v q).mp hqv
  have hqult : row a u q < 1 :=
    lt_of_le_of_ne (hu q) (fun h => hqu ((mem_active a u q).mpr h))
  ext z
  constructor
  · rintro ⟨hz, hcommon⟩
    let t : ℝ := (1 - row a z r) / (1 - row a v r)
    have hden : 0 < 1 - row a v r := sub_pos.mpr hrvlt
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hz r)) hden.le
    have hteq : t * (1 - row a v r) = 1 - row a z r := by
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    have hzline : z = u + t • (v-u) := by
      apply hinj
      funext i
      change row a z i.val = row a (u + t • (v-u)) i.val
      rw [row_add, row_smul, row_sub]
      by_cases hir : i.val = r
      · rw [hir, hru1]
        nlinarith [hteq]
      · have hiu : i.val ∈ (active a u).erase r :=
          Finset.mem_erase.mpr ⟨hir, i.property⟩
        rw [← her] at hiu
        have hiv1 : row a v i.val = 1 :=
          (mem_active a v i.val).mp (Finset.mem_inter.mp hiu).2
        have hiu1 : row a u i.val = 1 := (mem_active a u i.val).mp i.property
        rw [hcommon i.val hiu, hiu1, hiv1]
        ring
    have ht1 : t ≤ 1 := by
      have hq := hz q
      rw [hzline, row_add, row_smul, row_sub, hqv1] at hq
      by_contra hn
      have htgt : 1 < t := lt_of_not_ge hn
      have hp := mul_pos (sub_pos.mpr htgt) (sub_pos.mpr hqult)
      nlinarith
    refine ⟨1-t, t, sub_nonneg.mpr ht1, ht0, by ring, ?_⟩
    rw [hzline]
    module
  · intro hz
    obtain ⟨s, t, hs, ht, hst, heq⟩ := hz
    constructor
    · intro i
      have h1 := mul_le_mul_of_nonneg_left (hu i) hs
      have h2 := mul_le_mul_of_nonneg_left (hv i) ht
      rw [← heq, row_add, row_smul, row_smul]
      nlinarith
    · intro i hi
      have h := Finset.mem_inter.mp hi
      rw [← heq, row_add, row_smul, row_smul,
        (mem_active a u i).mp h.1, (mem_active a v i).mp h.2]
      nlinarith

/-- Along the open segment exactly the common ORIGINAL inequalities are tight.
This does not require a cardinality or independence premise. -/
theorem interior_tight_rows {d m : ℕ} (a : Fin m → ℝ) (u v : Fin d → ℝ)
    (hu : ∀ i, row a u i ≤ 1) (hv : ∀ i, row a v i ≤ 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    active a ((1-t) • u + t • v) = active a u ∩ active a v := by
  classical
  ext i
  simp only [mem_active, Finset.mem_inter, row_add, row_smul]
  constructor
  · intro he
    have hp := mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hu i))
    have hq := mul_nonneg ht.le (sub_nonneg.mpr (hv i))
    have hz1 : (1-t)*(1-row a u i)=0 := by nlinarith
    have hz2 : t*(1-row a v i)=0 := by nlinarith
    have hx1 := (mul_eq_zero.mp hz1).resolve_left (ne_of_gt (sub_pos.mpr ht1))
    have hx2 := (mul_eq_zero.mp hz2).resolve_left (ne_of_gt ht)
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    ring

noncomputable def rowSum {d m : ℕ} (a : Fin m → ℝ) (C : Finset (Fin m)) :
    (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i ∈ C, row a x i
  map_add' x y := by
    simp only [row_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [row_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]

lemma sum_rows_le {d m : ℕ} (a : Fin m → ℝ) (C : Finset (Fin m))
    (x : Fin d → ℝ) (hx : ∀ i, row a x i ≤ 1) :
    (∑ i ∈ C, row a x i) ≤ (C.card : ℝ) := by
  calc
    (∑ i ∈ C, row a x i) ≤ ∑ _i ∈ C, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hx i)
    _ = (C.card : ℝ) := by simp

lemma sum_rows_eq_iff {d m : ℕ} (a : Fin m → ℝ) (C : Finset (Fin m))
    (x : Fin d → ℝ) (hx : ∀ i, row a x i ≤ 1) :
    (∑ i ∈ C, row a x i) = (C.card : ℝ) ↔ ∀ i ∈ C, row a x i = 1 := by
  classical
  constructor
  · intro he i hi
    have hsum : ∑ j ∈ C, (1-row a x j) = 0 := by
      rw [Finset.sum_sub_distrib, he]
      simp
    have hi0 : 1-row a x i ≤ ∑ j ∈ C, (1-row a x j) :=
      Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hx j)) hi
    rw [hsum] at hi0
    linarith [hx i]
  · intro h
    calc
      (∑ i ∈ C, row a x i) = ∑ _i ∈ C, (1 : ℝ) := Finset.sum_congr rfl h
      _ = (C.card : ℝ) := by simp

/-- This is Mathlib exposedness of the ENTIRE closed segment, not just equal
endpoint objective values. The objective is the sum of the original common rows. -/
theorem exposed_edge {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (u v : Fin d → ℝ)
    (hu : ∀ i, row a u i ≤ 1) (hv : ∀ i, row a v i ≤ 1)
    (huc : (active a u).card = d) (hvc : (active a v).card = d)
    (hc : (active a u ∩ active a v).card + 1 = d) :
    IsExposed ℝ {z : Fin d → ℝ | ∀ i, row a z i ≤ 1} (segment ℝ u v) := by
  classical
  let C := active a u ∩ active a v
  have heq := common_slice_eq_segment a ha hm u v hu hv huc hvc hc
  have huC : ∀ i ∈ C, row a u i = 1 := by
    intro i hi
    exact (mem_active a u i).mp (Finset.mem_inter.mp hi).1
  have huSum : (∑ i ∈ C, row a u i) = (C.card : ℝ) :=
    (sum_rows_eq_iff a C u hu).mpr huC
  intro _
  refine ⟨LinearMap.toContinuousLinearMap (rowSum a C), ?_⟩
  ext z
  constructor
  · intro hz
    have hzC : (∀ i, row a z i ≤ 1) ∧ ∀ i ∈ C, row a z i = 1 := by
      rw [← heq] at hz
      exact hz
    refine ⟨hzC.1, ?_⟩
    intro w hw
    change (∑ i ∈ C, row a w i) ≤ ∑ i ∈ C, row a z i
    rw [(sum_rows_eq_iff a C z hzC.1).mpr hzC.2]
    exact sum_rows_le a C w hw
  · rintro ⟨hz, hmax⟩
    have hzu := hmax u hu
    change (∑ i ∈ C, row a u i) ≤ ∑ i ∈ C, row a z i at hzu
    rw [huSum] at hzu
    have hs : (∑ i ∈ C, row a z i) = (C.card : ℝ) :=
      le_antisymm (sum_rows_le a C z hz) hzu
    rw [← heq]
    exact ⟨hz, (sum_rows_eq_iff a C z hz).mp hs⟩

end Hirsch.MomentEdges

/-! New work: construct a neighbor rather than assume both edge endpoints. -/
namespace Hirsch.MomentRelease

open Set MomentBarycentric MomentVertices

/-- A finite first-blocking ratio is derived from strict slack and positive
slopes. The whole feasible nonnegative ray interval is characterized. -/
theorem first_blocker {ι : Type*} [Fintype ι] (v c : ι → ℝ)
    (hv : ∀ i, v i ≤ 1)
    (hactive : ∀ i, v i = 1 → c i ≤ 0)
    (hex : ∃ i, 0 < c i) :
    ∃ (t : ℝ) (q : ι), 0 < t ∧ 0 < c q ∧ v q < 1 ∧
      t = (1-v q)/c q ∧
      (∀ i, 0 < c i → t ≤ (1-v i)/c i) ∧
      (∀ i, v i+t*c i ≤ 1) ∧ v q+t*c q = 1 ∧
      (∀ s : ℝ, 0 ≤ s → ((∀ i, v i+s*c i ≤ 1) ↔ s ≤ t)) := by
  classical
  let B : Finset ι := Finset.univ.filter (fun i => 0 < c i)
  have hB : B.Nonempty := by
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  obtain ⟨q,hq,hmin⟩ := B.exists_min_image (fun i => (1-v i)/c i) hB
  have hcq : 0 < c q := (Finset.mem_filter.mp hq).2
  have hstrict : ∀ i, 0 < c i → v i < 1 := by
    intro i hi
    apply lt_of_le_of_ne (hv i)
    intro he
    have hh := hactive i he
    linarith
  let t : ℝ := (1-v q)/c q
  have ht : 0 < t := div_pos (sub_pos.mpr (hstrict q hcq)) hcq
  have hsmall : ∀ i, 0 < c i → t ≤ (1-v i)/c i := by
    intro i hi
    exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
  have hfeas : ∀ s : ℝ, 0 ≤ s → s ≤ t → ∀ i, v i+s*c i ≤ 1 := by
    intro s hs hst i
    by_cases hi : 0 < c i
    · have hle : s ≤ (1-v i)/c i := hst.trans (hsmall i hi)
      have hmul : s*c i ≤ 1-v i := (le_div_iff₀ hi).mp hle
      linarith
    · have hnon := mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_gt hi)
      linarith [hv i]
  have hblock : v q+t*c q = 1 := by
    have he : t*c q = 1-v q := div_mul_cancel₀ _ (ne_of_gt hcq)
    linarith
  refine ⟨t,q,ht,hcq,hstrict q hcq,rfl,hsmall,hfeas t ht.le le_rfl,hblock,?_⟩
  intro s hs
  constructor
  · intro hf
    have hmul : s*c q ≤ 1-v q := by linarith [hf q]
    exact (le_div_iff₀ hcq).mpr hmul
  · exact hfeas s hs

/-- Releasing any tight row yields a normalized direction. A positive blocker
exists because the centered original rows sum to zero. -/
theorem release_direction {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (u : Fin d → ℝ)
    (p : Fin m) (hp : p ∈ active a u) :
    ∃ w : Fin d → ℝ,
      row a w p = -1 ∧
      (∀ i ∈ (active a u).erase p, row a w i = 0) ∧
      (∀ i, row a u i = 1 → row a w i ≤ 0) ∧
      ∃ q, 0 < row a w q := by
  classical
  let values : (active a u) → ℝ := fun i => if i.val = p then -1 else 0
  obtain ⟨w,hw⟩ := activeEval_surjective a ha hm u values
  have hrows : ∀ i ∈ active a u, row a w i = if i = p then -1 else 0 := by
    intro i hi
    exact congrFun hw ⟨i,hi⟩
  have hpw : row a w p = -1 := by simpa only [if_pos rfl] using hrows p hp
  have hzero : ∀ i ∈ (active a u).erase p, row a w i = 0 := by
    intro i hi
    exact (hrows i (Finset.mem_erase.mp hi).2).trans
      (if_neg (Finset.mem_erase.mp hi).1)
  have hnon : ∀ i, row a u i = 1 → row a w i ≤ 0 := by
    intro i hi
    rw [hrows i ((mem_active a u i).mpr hi)]
    split_ifs <;> norm_num
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hex : ∃ q, 0 < row a w q := by
    by_contra hn
    push_neg at hn
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin m => -row a w i)
      (fun i _ => neg_nonneg.mpr (hn i)) (Finset.mem_univ p)
    rw [Finset.sum_neg_distrib, sum_row_zero a w hm0, neg_zero] at hle
    change -row a w p ≤ 0 at hle
    rw [hpw] at hle
    norm_num at hle
  exact ⟨w,hpw,hzero,hnon,hex⟩

/-- Construct the next actual vertex, unique new tight label, and entire
exposed original edge after releasing any one original active row. -/
theorem release_edge {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (u : Fin d → ℝ)
    (hu : u ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ)
    (p : Fin m) (hp : p ∈ active a u) :
    ∃ (w : Fin d → ℝ) (t : ℝ) (q : Fin m),
      0 < t ∧ q ∉ active a u ∧
      row a w p = -1 ∧ (∀ i ∈ (active a u).erase p, row a w i = 0) ∧
      0 < row a w q ∧ t = (1-row a u q)/row a w q ∧
      (∀ i, 0 < row a w i → t ≤ (1-row a u i)/row a w i) ∧
      u + t • w ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ ∧
      active a (u+t • w) = insert q ((active a u).erase p) ∧
      u ≠ u+t • w ∧
      IsExposed ℝ {x : Fin d → ℝ | ∀ i, row a x i ≤ 1} (segment ℝ u (u+t • w)) ∧
      IsExtreme ℝ {x : Fin d → ℝ | ∀ i, row a x i ≤ 1} (segment ℝ u (u+t • w)) ∧
      {z : Fin d → ℝ | (∀ i, row a z i ≤ 1) ∧
        ∀ i ∈ (active a u).erase p, row a z i = 1} = segment ℝ u (u+t • w) ∧
      (∀ s : ℝ, 0 ≤ s → ((∀ i, row a (u+s • w) i ≤ 1) ↔ s ≤ t)) := by
  classical
  have huc : (active a u).card = d := ((extreme_iff_tight_card a ha hm u).mp hu).2
  obtain ⟨w,hpw,hzero,hnon,hpos⟩ := release_direction a ha hm u p hp
  obtain ⟨t,q,ht,hcq,hqu,htq,hmin,hfeas,hblock,hray⟩ :=
    first_blocker (row a u) (row a w) hu.1 hnon hpos
  let v : Fin d → ℝ := u+t • w
  have hvrow : ∀ i, row a v i = row a u i+t*row a w i := by
    intro i
    exact (row_add a u (t • w) i).trans (by rw [row_smul])
  have hv : ∀ i, row a v i ≤ 1 := by intro i; rw [hvrow]; exact hfeas i
  have hqnot : q ∉ active a u := by
    intro hi
    have he := (mem_active a u q).mp hi
    linarith
  have hpu : row a u p = 1 := (mem_active a u p).mp hp
  have hpv : row a v p < 1 := by rw [hvrow,hpu,hpw]; linarith
  have hqv : q ∈ active a v := by
    apply (mem_active a v q).mpr
    rw [hvrow]
    exact hblock
  have hkeep : (active a u).erase p ⊆ active a v := by
    intro i hi
    apply (mem_active a v i).mpr
    rw [hvrow,hzero i hi,(mem_active a u i).mp (Finset.mem_erase.mp hi).2]
    ring
  have hqerase : q ∉ (active a u).erase p := by
    intro hi
    exact hqnot (Finset.mem_erase.mp hi).2
  have hSc : (insert q ((active a u).erase p)).card = d := by
    rw [Finset.card_insert_of_notMem hqerase,Finset.card_erase_of_mem hp,huc]
    have hd : 0 < d := by
      have hh := Finset.card_pos.mpr ⟨p,hp⟩
      omega
    omega
  have hsub : insert q ((active a u).erase p) ⊆ active a v :=
    Finset.insert_subset_iff.mpr ⟨hqv,hkeep⟩
  have hact : active a v = insert q ((active a u).erase p) := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hSc]
    exact tight_card_le a ha hm v
  have hvc : (active a v).card = d := by rw [hact,hSc]
  have hcommon : active a u ∩ active a v = (active a u).erase p := by
    rw [hact]
    ext i
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨hi,he | he⟩
      · subst i
        exact False.elim (hqnot hi)
      · exact he
    · intro hi
      exact ⟨(Finset.mem_erase.mp hi).2,Or.inr hi⟩
  have hc : (active a u ∩ active a v).card+1 = d := by
    rw [hcommon,Finset.card_erase_of_mem hp,huc]
    have hd : 0 < d := by have hh := Finset.card_pos.mpr ⟨p,hp⟩; omega
    omega
  have hve := (extreme_iff_tight_card a ha hm v).mpr ⟨hv,hvc⟩
  have hne : u ≠ v := by intro he; have hh : row a v p = 1 := he ▸ hpu; linarith
  have hedge := MomentEdges.exposed_edge a ha hm u v hu.1 hv huc hvc hc
  have hslice := MomentEdges.common_slice_eq_segment a ha hm u v hu.1 hv huc hvc hc
  rw [hcommon] at hslice
  refine ⟨w,t,q,ht,hqnot,hpw,hzero,hcq,htq,hmin,hve,hact,hne,
    hedge,hedge.isExtreme,hslice,?_⟩
  intro s hs
  simpa only [row_add,row_smul] using hray s hs

end Hirsch.MomentRelease


namespace Hirsch.MomentRootCatalogue

open Set MomentBarycentric MomentVertices

noncomputable def rootPoly {m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) :
    Polynomial ℝ := ∏ i ∈ S, (Polynomial.X - Polynomial.C (a i))

lemma eval_rootPoly {m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) (t : ℝ) :
    (rootPoly a S).eval t = ∏ i ∈ S, (t-a i) := by
  classical
  simp [rootPoly, Polynomial.eval_prod]

lemma degree_rootPoly {m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) :
    (rootPoly a S).natDegree = S.card := by
  classical
  change (∏ i ∈ S, ((Polynomial.X : Polynomial ℝ) - Polynomial.C (a i))).natDegree = S.card
  rw [Polynomial.natDegree_prod_of_monic S
    (fun i : Fin m => ((Polynomial.X : Polynomial ℝ) - Polynomial.C (a i)))
    (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp

lemma eval_rootPoly_zero_iff {m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (S : Finset (Fin m)) (i : Fin m) :
    (rootPoly a S).eval (a i) = 0 ↔ i ∈ S := by
  classical
  rw [eval_rootPoly]
  constructor
  · intro h
    obtain ⟨j,hj,hzero⟩ := Finset.prod_eq_zero_iff.mp h
    have hij : i = j := ha (sub_eq_zero.mp hzero)
    exact hij.symm ▸ hj
  · intro hi
    exact Finset.prod_eq_zero_iff.mpr ⟨i,hi,sub_self _⟩

noncomputable def mean {m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  (∑ i : Fin m, (rootPoly a S).eval (a i)) / (m : ℝ)

noncomputable def candidate {d m : ℕ} (a : Fin m → ℝ)
    (S : Finset (Fin m)) : Fin d → ℝ :=
  fun j => -(rootPoly a S).coeff (j.val+1) / mean a S

/-- The same full-label mean is used in both the coefficient formula and all
original inequalities. No positivity of that mean is assumed. -/
lemma row_candidate {d m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m))
    (hS : S.card ≤ d) (hm : (m : ℝ) ≠ 0) (hmean : mean a S ≠ 0) (i : Fin m) :
    row a (candidate (d:=d) a S) i = 1 - (rootPoly a S).eval (a i) / mean a S := by
  classical
  have hdeg : (rootPoly a S).natDegree ≤ d := by rw [degree_rootPoly]; exact hS
  have hm' : (Fintype.card (Fin m) : ℝ) ≠ 0 := by simpa only [Fintype.card_fin] using hm
  have hc := MomentSmallFaces.centered_eval a (rootPoly a S) d hdeg hm' i
  have hc' : (∑ j : Fin d,
      (a i ^ (j.val+1) - (∑ l, a l ^ (j.val+1)) / (m : ℝ)) *
        (rootPoly a S).coeff (j.val+1)) = (rootPoly a S).eval (a i) - mean a S := by
    simpa only [Fintype.card_fin, mean] using hc
  calc
    row a (candidate (d:=d) a S) i =
        -(mean a S)⁻¹ * (∑ j : Fin d,
          (a i ^ (j.val+1) - (∑ l, a l ^ (j.val+1)) / (m : ℝ)) *
            (rootPoly a S).coeff (j.val+1)) := by
      unfold row candidate
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -(mean a S)⁻¹ * ((rootPoly a S).eval (a i) - mean a S) := by rw [hc']
    _ = 1 - (rootPoly a S).eval (a i) / mean a S := by
      field_simp [hmean]
      <;> ring

lemma active_candidate {d m : ℕ} (a : Fin m → ℝ) (ha : Function.Injective a)
    (S : Finset (Fin m)) (hS : S.card ≤ d) (hm : (m : ℝ) ≠ 0)
    (hmean : mean a S ≠ 0) : active a (candidate (d:=d) a S) = S := by
  classical
  ext i
  rw [mem_active, row_candidate a S hS hm hmean i]
  constructor
  · intro h
    have hquot : (rootPoly a S).eval (a i) / mean a S = 0 := by linarith
    have hmul := div_mul_cancel₀ ((rootPoly a S).eval (a i)) hmean
    rw [hquot, zero_mul] at hmul
    exact (eval_rootPoly_zero_iff a ha S i).mp hmul.symm
  · intro hi
    rw [(eval_rootPoly_zero_iff a ha S i).mpr hi, zero_div, sub_zero]

/-- A zero full-label mean would provide a nonzero active-kernel motion. The
accepted extremality theorem excludes it, including in dimension zero. -/
theorem extreme_mean_ne_zero {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ)
    (hx : x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ) :
    mean a (active a x) ≠ 0 := by
  classical
  let S := active a x
  have hS : S.card = d := ((extreme_iff_tight_card a ha hm x).mp hx).2
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hm' : (Fintype.card (Fin m) : ℝ) ≠ 0 := by simpa only [Fintype.card_fin] using hm0
  have hdeg : (rootPoly a S).natDegree ≤ d := by rw [degree_rootPoly,hS]
  let y : Fin d → ℝ := fun j => (rootPoly a S).coeff (j.val+1)
  have he : ∀ i : Fin m, row a y i = (rootPoly a S).eval (a i) - mean a S := by
    intro i
    simpa only [row,y,mean,Fintype.card_fin] using
      MomentSmallFaces.centered_eval a (rootPoly a S) d hdeg hm' i
  intro hzero
  change mean a S = 0 at hzero
  have hy : y = 0 := by
    apply extreme_kernel a x hx y
    intro i hi
    rw [he, hzero, sub_zero]
    exact (eval_rootPoly_zero_iff a ha S i).mpr ((mem_active a x i).mpr hi)
  obtain ⟨i,hi⟩ : ∃ i : Fin m, i ∉ S := by
    by_contra hn
    have hall : (Finset.univ : Finset (Fin m)) ⊆ S := by
      intro i _
      by_contra hi
      exact hn ⟨i,hi⟩
    have hc := Finset.card_le_card hall
    simp only [Finset.card_univ,Fintype.card_fin,hS] at hc
    omega
  have hr : row a y i = 0 := by rw [hy]; simp [row]
  rw [he, hzero, sub_zero] at hr
  exact hi ((eval_rootPoly_zero_iff a ha S i).mp hr)

/-- Every actual vertex equals the explicit coefficient candidate on its own
exact tight set. No inversion, supplied vertex list or root-factorization oracle. -/
theorem reconstruct_extreme {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ)
    (hx : x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ) :
    candidate (d:=d) a (active a x) = x := by
  classical
  have hS := ((extreme_iff_tight_card a ha hm x).mp hx).2
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hmean := extreme_mean_ne_zero a ha hm x hx
  apply extreme_activeEval_injective a x hx
  funext i
  change row a (candidate (d:=d) a (active a x)) i.val = row a x i.val
  rw [row_candidate a (active a x) hS.le hm0 hmean i.val,
    (eval_rootPoly_zero_iff a ha (active a x) i.val).mpr i.property,
    zero_div,sub_zero]
  exact ((mem_active a x i.val).mp i.property).symm

noncomputable def catalogue (d : ℕ) {m : ℕ} (a : Fin m → ℝ) :
    Finset (Finset (Fin m)) :=
  (Finset.powersetCard d Finset.univ).filter
    (fun S => mean a S ≠ 0 ∧ ∀ i : Fin m, 0 ≤ (rootPoly a S).eval (a i) / mean a S)

lemma mem_catalogue {d m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) :
    S ∈ catalogue d a ↔ S.card = d ∧ mean a S ≠ 0 ∧
      ∀ i : Fin m, 0 ≤ (rootPoly a S).eval (a i) / mean a S := by
  classical
  simp [catalogue, Finset.mem_powersetCard, and_assoc]

/-- The explicit finite filter returns exactly every original extreme point,
with no duplicate candidates. It is not asserted polynomial in dimension. -/
theorem complete_catalogue {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) :
    Set.InjOn (candidate (d:=d) a) (catalogue d a) ∧
    (∀ x : Fin d → ℝ,
      x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ ↔
        x ∈ (catalogue d a).image (candidate (d:=d) a)) ∧
    (∀ S ∈ catalogue d a, ∀ i : Fin m,
      row a (candidate (d:=d) a S) i = 1 ↔ i ∈ S) ∧
    ((catalogue d a).image (candidate (d:=d) a)).card = (catalogue d a).card ∧
    (catalogue d a).card ≤ Nat.choose m d := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hact : ∀ S ∈ catalogue d a, active a (candidate (d:=d) a S) = S := by
    intro S hS
    obtain ⟨hc,hmn,hnon⟩ := (mem_catalogue a S).mp hS
    exact active_candidate a ha S hc.le hm0 hmn
  have hinj : Set.InjOn (candidate (d:=d) a) (catalogue d a) := by
    intro S hS T hT he
    calc
      S = active a (candidate (d:=d) a S) := (hact S hS).symm
      _ = active a (candidate (d:=d) a T) := congrArg (active a) he
      _ = T := hact T hT
  refine ⟨hinj,?_,?_,Finset.card_image_of_injOn hinj,?_⟩
  · intro x
    constructor
    · intro hx
      have hS := ((extreme_iff_tight_card a ha hm x).mp hx).2
      have hmean := extreme_mean_ne_zero a ha hm x hx
      have he := reconstruct_extreme a ha hm x hx
      have hmem : active a x ∈ catalogue d a := by
        apply (mem_catalogue a (active a x)).mpr
        refine ⟨hS,hmean,?_⟩
        intro i
        have hv := row_candidate a (active a x) hS.le hm0 hmean i
        rw [he] at hv
        linarith [hx.1 i]
      exact Finset.mem_image.mpr ⟨active a x,hmem,he⟩
    · intro hx
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hc,hmn,hnon⟩ := (mem_catalogue a S).mp hS
      apply (extreme_iff_tight_card a ha hm _).mpr
      constructor
      · intro i
        rw [row_candidate a S hc.le hm0 hmn i]
        linarith [hnon i]
      · rw [hact S hS]
        exact hc
  · intro S hS i
    rw [← mem_active, hact S hS]
  · have hsub : catalogue d a ⊆ Finset.powersetCard d (Finset.univ : Finset (Fin m)) := by
      intro S hS
      exact (Finset.mem_filter.mp hS).1
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using hc

end Hirsch.MomentRootCatalogue


namespace Hirsch.MomentMonotone

open Set MomentBarycentric MomentVertices MomentEdges

lemma row_finite_sum {d m : ℕ} {J : Type*} [Fintype J]
    (a : Fin m → ℝ) (z : J → (Fin d → ℝ)) (i : Fin m) :
    row a (∑ j, z j) i = ∑ j, row a (z j) i := by
  simp only [row, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Feasible target displacement is a nonnegative combination of the normalized
release directions. A positive objective gain therefore supplies an improving
original edge, without an improving-pivot oracle. -/
theorem improving_pivot {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (u v : Fin d → ℝ)
    (hu : u ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ)
    (hv : ∀ i, row a v i ≤ 1) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hgain : f u < f v) :
    ∃ z : Fin d → ℝ,
      z ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ ∧
      f u < f z ∧
      IsExposed ℝ {x : Fin d → ℝ | ∀ i, row a x i ≤ 1} (segment ℝ u z) ∧
      ∀ i : Fin m, row a u i = 1 → row a v i = 1 → row a z i = 1 := by
  classical
  let I := ↥(active a u)
  have hd : ∀ p : I, ∃ (w : Fin d → ℝ) (t : ℝ), 0 < t ∧
      (∀ i : I, row a w i.val = if i = p then -1 else 0) ∧
      u + t • w ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ ∧
      IsExposed ℝ {x : Fin d → ℝ | ∀ i, row a x i ≤ 1} (segment ℝ u (u + t • w)) := by
    intro p
    obtain ⟨w,t,q,ht,hq,hpw,hzero,hcq,htr,hmin,hve,hact,hne,hexposed,hxe,hslice,hray⟩ :=
      MomentRelease.release_edge a ha hm u hu p.val p.property
    refine ⟨w,t,ht,?_,hve,hexposed⟩
    intro i
    by_cases hip : i = p
    · subst i
      simpa only [if_pos rfl] using hpw
    · have hval : i.val ≠ p.val := fun he => hip (Subtype.ext he)
      rw [if_neg hip]
      exact hzero i.val (Finset.mem_erase.mpr ⟨hval,i.property⟩)
  choose w t ht hnorm hext hedge using hd
  let c : I → ℝ := fun i => 1 - row a v i.val
  have hc : ∀ i, 0 ≤ c i := fun i => sub_nonneg.mpr (hv i.val)
  have hdecomp : v - u = ∑ p : I, c p • w p := by
    apply extreme_activeEval_injective a u hu
    funext i
    change row a (v-u) i.val = row a (∑ p : I, c p • w p) i.val
    rw [row_sub, row_finite_sum]
    simp_rw [row_smul]
    have hsum : (∑ p : I, c p * row a (w p) i.val) = -c i := by
      calc
        (∑ p : I, c p * row a (w p) i.val) = c i * row a (w i) i.val := by
          apply Finset.sum_eq_single i
          · intro p _ hpi
            rw [hnorm p i, if_neg (Ne.symm hpi), mul_zero]
          · intro hn
            exact False.elim (hn (Finset.mem_univ i))
        _ = -c i := by rw [hnorm i i, if_pos rfl]; ring
    rw [hsum, (mem_active a u i.val).mp i.property]
    dsimp only [c]
    ring
  have hpositive : 0 < ∑ p : I, c p * f (w p) := by
    have he := congrArg f hdecomp
    simp only [map_sub, map_sum, map_smul, smul_eq_mul] at he
    linarith
  obtain ⟨p,hp⟩ : ∃ p : I, 0 < c p * f (w p) := by
    by_contra hn
    push_neg at hn
    have hz : (∑ p : I, c p * f (w p)) ≤ 0 :=
      Finset.sum_nonpos (fun p _ => hn p)
    linarith
  have hcp : 0 < c p := by
    by_contra hn
    have hz : c p = 0 := le_antisymm (le_of_not_gt hn) (hc p)
    rw [hz,zero_mul] at hp
    exact (lt_irrefl 0) hp
  have hfp : 0 < f (w p) := by
    by_contra hn
    have hz := mul_nonpos_of_nonneg_of_nonpos (hc p) (le_of_not_gt hn)
    linarith
  refine ⟨u + t p • w p,hext p,?_,hedge p,?_⟩
  · rw [map_add, map_smul, smul_eq_mul]
    exact lt_add_of_pos_right _ (mul_pos (ht p) hfp)
  · intro i hiu hiv
    let j : I := ⟨i,(mem_active a u i).mpr hiu⟩
    have hjp : j ≠ p := by
      intro he
      have hi : i = p.val := congrArg Subtype.val he
      have hvp : row a v p.val = 1 := hi ▸ hiv
      have hz : c p = 0 := by dsimp only [c]; rw [hvp]; ring
      linarith
    have hz : row a (w p) i = 0 := (hnorm p j).trans (if_neg hjp)
    rw [row_add, row_smul, hz, mul_zero, add_zero, hiu]

/-- Sum of the target's tight ORIGINAL rows uniquely exposes that target. -/
lemma target_score_strict {d m : ℕ} (a : Fin m → ℝ)
    (v : Fin d → ℝ)
    (hv : v ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ)
    (u : Fin d → ℝ) (hu : ∀ i, row a u i ≤ 1) (hne : u ≠ v) :
    rowSum a (active a v) u < rowSum a (active a v) v := by
  classical
  have hmax : (∑ i ∈ active a v, row a v i) = ((active a v).card : ℝ) :=
    (sum_rows_eq_iff a (active a v) v hv.1).mpr
      (fun i hi => (mem_active a v i).mp hi)
  change (∑ i ∈ active a v, row a u i) < ∑ i ∈ active a v, row a v i
  rw [hmax]
  apply lt_of_le_of_ne (sum_rows_le a (active a v) u hu)
  intro he
  have hrows := (sum_rows_eq_iff a (active a v) u hu).mp he
  apply hne
  apply extreme_activeEval_injective a v hv
  funext i
  change row a u i.val = row a v i.val
  exact (hrows i.val i.property).trans ((mem_active a v i.val).mp i.property).symm

/-- Finite strict ascent constructs an entire route. The finite upper bound is
not relabelled as a polynomial bound. No route is assumed. -/
lemma finite_ascent {E : Type*} (F : Finset E) (v : E) (f : E → ℝ)
    (edge : E → E → Prop)
    (hstep : ∀ u ∈ F, u ≠ v → ∃ w ∈ F, f u < f w ∧ edge u w)
    (u : E) (hu : u ∈ F) :
    ∃ L : ℕ, L < F.card ∧ ∃ p : ℕ → E,
      p 0 = u ∧ p L = v ∧ (∀ i, i ≤ L → p i ∈ F) ∧
      ∀ i, i < L → f (p i) < f (p (i+1)) ∧ edge (p i) (p (i+1)) := by
  classical
  have aux : ∀ n : ℕ, ∀ u ∈ F,
      (F.filter (fun z => f u < f z)).card ≤ n →
      ∃ L : ℕ, L ≤ n ∧ ∃ p : ℕ → E,
        p 0 = u ∧ p L = v ∧ (∀ i, i ≤ L → p i ∈ F) ∧
        ∀ i, i < L → f (p i) < f (p (i+1)) ∧ edge (p i) (p (i+1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hu hbudget
      by_cases huv : u = v
      · subst u
        refine ⟨0,Nat.zero_le _,fun _ => v,rfl,rfl,?_,?_⟩
        · intro i hi
          exact hu
        · intro i hi
          omega
      · obtain ⟨w,hw,hgain,hedge⟩ := hstep u hu huv
        have hwF : w ∈ F.filter (fun z => f u < f z) :=
          Finset.mem_filter.mpr ⟨hw,hgain⟩
        have hsub : F.filter (fun z => f w < f z) ⊆
            (F.filter (fun z => f u < f z)).erase w := by
          intro z hz
          obtain ⟨hzF,hzgt⟩ := Finset.mem_filter.mp hz
          refine Finset.mem_erase.mpr ⟨?_,Finset.mem_filter.mpr ⟨hzF,hgain.trans hzgt⟩⟩
          intro he
          subst z
          exact (lt_irrefl _) hzgt
        have hcard := Finset.card_le_card hsub
        have herase := Finset.card_erase_add_one hwF
        have hrank : (F.filter (fun z => f w < f z)).card < n := by omega
        obtain ⟨L,hL,p,hp0,hpL,hpm,hpe⟩ :=
          ih (F.filter (fun z => f w < f z)).card hrank w hw le_rfl
        let q : ℕ → E := fun i => match i with
          | 0 => u
          | j+1 => p j
        refine ⟨L+1,by omega,q,rfl,hpL,?_,?_⟩
        · intro i hi
          cases i with
          | zero => exact hu
          | succ i => exact hpm i (by omega)
        · intro i hi
          cases i with
          | zero => simpa only [q,hp0] using And.intro hgain hedge
          | succ i => exact hpe i (by omega)
  obtain ⟨L,hL,p,hp0,hpL,hpm,hpe⟩ :=
    aux (F.filter (fun z => f u < f z)).card u hu le_rfl
  have hsub : F.filter (fun z => f u < f z) ⊆ F.erase u := by
    intro z hz
    obtain ⟨hzF,hgt⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_erase.mpr ⟨?_,hzF⟩
    intro he
    subst z
    exact (lt_irrefl _) hgt
  have hc := Finset.card_le_card hsub
  have he := Finset.card_erase_add_one hu
  exact ⟨L,by omega,p,hp0,hpL,hpm,hpe⟩

/-- Arbitrary actual endpoints, including all normalization signs and odd
ambient dimensions, have a target-monotone original-edge route. -/
theorem all_endpoint_route {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (u v : Fin d → ℝ)
    (hu : u ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ)
    (hv : v ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ) :
    ∃ L : ℕ, L < Nat.choose m d ∧ ∃ p : ℕ → (Fin d → ℝ),
      p 0 = u ∧ p L = v ∧
      (∀ i, i ≤ L → p i ∈ ({x : Fin d → ℝ | ∀ j, row a x j ≤ 1}).extremePoints ℝ) ∧
      ∀ i, i < L →
        rowSum a (active a v) (p i) < rowSum a (active a v) (p (i+1)) ∧
        IsExposed ℝ {x : Fin d → ℝ | ∀ j, row a x j ≤ 1} (segment ℝ (p i) (p (i+1))) ∧
        ∀ j, row a (p i) j = 1 → row a v j = 1 → row a (p (i+1)) j = 1 := by
  classical
  obtain ⟨hinj,hcomplete,htight,hcard,hbound⟩ :=
    MomentRootCatalogue.complete_catalogue a ha hm
  let F := (MomentRootCatalogue.catalogue d a).image (MomentRootCatalogue.candidate (d:=d) a)
  let f : (Fin d → ℝ) →ₗ[ℝ] ℝ := rowSum a (active a v)
  let edge : (Fin d → ℝ) → (Fin d → ℝ) → Prop := fun x y =>
    IsExposed ℝ {z : Fin d → ℝ | ∀ i, row a z i ≤ 1} (segment ℝ x y) ∧
      ∀ i, row a x i = 1 → row a v i = 1 → row a y i = 1
  have hstep : ∀ x ∈ F, x ≠ v → ∃ y ∈ F, f x < f y ∧ edge x y := by
    intro x hx hne
    have hxe := (hcomplete x).mpr hx
    obtain ⟨y,hye,hgain,hedge,hkeep⟩ := improving_pivot a ha hm x v hxe hv.1 f
      (target_score_strict a v hv x hxe.1 hne)
    exact ⟨y,(hcomplete y).mp hye,hgain,hedge,hkeep⟩
  obtain ⟨L,hL,p,hp0,hpL,hpm,hpe⟩ := finite_ascent F v f edge hstep u ((hcomplete u).mp hu)
  have hF : F.card ≤ Nat.choose m d := hcard.trans_le hbound
  refine ⟨L,hL.trans_le hF,p,hp0,hpL,?_,hpe⟩
  intro i hi
  exact (hcomplete (p i)).mpr (hpm i hi)

end Hirsch.MomentMonotone

/-- Complete target-monotone original-edge routing between any two original
moment vertices. The proved finite bound may be exponential. -/
theorem solution (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let J : Finset (Fin m) := Finset.univ.filter (fun i => row v i = 1)
    let score : (Fin d → ℝ) → ℝ := fun x => ∑ i ∈ J, row x i
    u ∈ P.extremePoints ℝ → v ∈ P.extremePoints ℝ →
      ∃ L : ℕ, L < Nat.choose m d ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0 = u ∧ p L = v ∧
        (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → score (p i) < score (p (i+1)) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          ∀ j, row (p i) j = 1 → row v j = 1 → row (p (i+1)) j = 1 := by
  dsimp only
  intro hu hv
  exact Hirsch.MomentMonotone.all_endpoint_route a ha hm u v hu hv

#print axioms Hirsch.MomentMonotone.improving_pivot
#print axioms Hirsch.MomentMonotone.target_score_strict
#print axioms Hirsch.MomentMonotone.finite_ascent
#print axioms Hirsch.MomentMonotone.all_endpoint_route
#print axioms solution
