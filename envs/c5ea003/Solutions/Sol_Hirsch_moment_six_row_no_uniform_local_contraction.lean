-- Prove2me | solution 1 for Hirsch.moment_six_row_no_uniform_local_contraction
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-18T20:33:29.862984+00:00
-- url     : https://prove2.me/submissions/07282fd9-6960-4e2e-bb91-c94a4d994362

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

namespace Hirsch.SmallGain

open Set MomentBarycentric MomentVertices MomentEdges

private def nodes (e : ℝ) : Fin 6 → ℝ := ![-1, 0, e, 2*e, 3*e, 1]

private def pt (e : ℝ) : Fin 5 → (Fin 2 → ℝ) :=
  ![![9*e/(1+4*e^2), -3/(1+4*e^2)],
    ![3*e/(1+4*e^2), -3/(1+4*e^2)],
    ![15*e/(1+10*e^2), -3/(1+10*e^2)],
    ![0, 3/(2-7*e^2)],
    ![-3/(1+3*e+7*e^2), -3/(1+3*e+7*e^2)]]

private def roots : Fin 5 → Finset (Fin 6) :=
  ![{2,3}, {1,2}, {3,4}, {0,5}, {0,1}]

private def sl (e : ℝ) : Fin 5 → (Fin 6 → ℝ) :=
  ![![3*(e+1)*(2*e+1)/(1+4*e^2), 6*e^2/(1+4*e^2), 0, 0,
       6*e^2/(1+4*e^2), 3*(1-e)*(1-2*e)/(1+4*e^2)],
    ![3*(e+1)/(1+4*e^2), 0, 0, 6*e^2/(1+4*e^2),
       18*e^2/(1+4*e^2), 3*(1-e)/(1+4*e^2)],
    ![3*(2*e+1)*(3*e+1)/(1+10*e^2), 18*e^2/(1+10*e^2),
       6*e^2/(1+10*e^2), 0, 0, 3*(1-2*e)*(1-3*e)/(1+10*e^2)],
    ![0, 3/(2-7*e^2), 3*(1-e)*(1+e)/(2-7*e^2),
       3*(1-2*e)*(1+2*e)/(2-7*e^2), 3*(1-3*e)*(1+3*e)/(2-7*e^2), 0],
    ![0, 0, 3*e*(e+1)/(1+3*e+7*e^2), 6*e*(2*e+1)/(1+3*e+7*e^2),
       9*e*(3*e+1)/(1+3*e+7*e^2), 6/(1+3*e+7*e^2)]]

private lemma parameter_bounds (e : ℝ) (he : 0 < e) (he4 : e < 1/4) :
    e^2 < 1/16 ∧ 0 < 1-e ∧ 0 < 1-2*e ∧ 0 < 1-3*e ∧
    0 < 1+4*e^2 ∧ 0 < 1+10*e^2 ∧ 0 < 2-7*e^2 ∧ 0 < 1+3*e+7*e^2 := by
  have hp : 0 < e*(1/4-e) := mul_pos he (by linarith)
  have he2 : e^2 < 1/16 := by nlinarith
  exact ⟨he2, by linarith, by linarith, by linarith,
    by positivity, by positivity, by nlinarith, by positivity⟩

private lemma nodes_injective (e : ℝ) (he : 0 < e) (he4 : e < 1/4) :
    Function.Injective (nodes e) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
  | rfl
  | (norm_num [nodes] at hij <;> linarith)

private lemma row_formula (e : ℝ) (x : Fin 2 → ℝ) (i : Fin 6) :
    row (nodes e) x i = (nodes e i-e)*x 0 +
      ((nodes e i)^2-(1+7*e^2)/3)*x 1 := by
  fin_cases i <;> norm_num [row, nodes, Fin.sum_univ_succ] <;> ring

/-- Every original inequality is evaluated, not only the active rows. -/
private lemma slack_table (e : ℝ) (he : 0 < e) (he4 : e < 1/4)
    (p : Fin 5) (i : Fin 6) :
    1-row (nodes e) (pt e p) i = sl e p i := by
  obtain ⟨he2,h1,h2,h3,hD,hE,hF,hG⟩ := parameter_bounds e he he4
  have hF' : (2 - e^2*7 : ℝ) ≠ 0 := by nlinarith
  rw [row_formula]
  fin_cases p <;> fin_cases i <;> norm_num [pt, sl, nodes] <;>
    field_simp [ne_of_gt hD, ne_of_gt hE, ne_of_gt hF, hF', ne_of_gt hG] <;> ring

private lemma slack_spec (e : ℝ) (he : 0 < e) (he4 : e < 1/4)
    (p : Fin 5) (i : Fin 6) :
    0 ≤ sl e p i ∧ (sl e p i = 0 ↔ i ∈ roots p) := by
  obtain ⟨he2,h1,h2,h3,hD,hE,hF,hG⟩ := parameter_bounds e he he4
  by_cases hi : i ∈ roots p
  · have hz : sl e p i = 0 := by
      fin_cases p <;> fin_cases i <;> first
      | rfl
      | (exfalso; revert hi; decide)
    exact ⟨by simpa only [hz] using (le_refl (0 : ℝ)), iff_of_true hz hi⟩
  · have hs : 0 < sl e p i := by
      fin_cases p
      · fin_cases i
        · change (0 : ℝ) < 3*(e+1)*(2*e+1)/(1+4*e^2)
          positivity
        · change (0 : ℝ) < 6*e^2/(1+4*e^2)
          positivity
        · exact False.elim (hi (by decide))
        · exact False.elim (hi (by decide))
        · change (0 : ℝ) < 6*e^2/(1+4*e^2)
          positivity
        · change (0 : ℝ) < 3*(1-e)*(1-2*e)/(1+4*e^2)
          positivity
      · fin_cases i
        · change (0 : ℝ) < 3*(e+1)/(1+4*e^2)
          positivity
        · exact False.elim (hi (by decide))
        · exact False.elim (hi (by decide))
        · change (0 : ℝ) < 6*e^2/(1+4*e^2)
          positivity
        · change (0 : ℝ) < 18*e^2/(1+4*e^2)
          positivity
        · change (0 : ℝ) < 3*(1-e)/(1+4*e^2)
          positivity
      · fin_cases i
        · change (0 : ℝ) < 3*(2*e+1)*(3*e+1)/(1+10*e^2)
          positivity
        · change (0 : ℝ) < 18*e^2/(1+10*e^2)
          positivity
        · change (0 : ℝ) < 6*e^2/(1+10*e^2)
          positivity
        · exact False.elim (hi (by decide))
        · exact False.elim (hi (by decide))
        · change (0 : ℝ) < 3*(1-2*e)*(1-3*e)/(1+10*e^2)
          positivity
      · fin_cases i
        · exact False.elim (hi (by decide))
        · change (0 : ℝ) < 3/(2-7*e^2)
          positivity
        · change (0 : ℝ) < 3*(1-e)*(1+e)/(2-7*e^2)
          positivity
        · change (0 : ℝ) < 3*(1-2*e)*(1+2*e)/(2-7*e^2)
          positivity
        · change (0 : ℝ) < 3*(1-3*e)*(1+3*e)/(2-7*e^2)
          positivity
        · exact False.elim (hi (by decide))
      · fin_cases i
        · exact False.elim (hi (by decide))
        · exact False.elim (hi (by decide))
        · change (0 : ℝ) < 3*e*(e+1)/(1+3*e+7*e^2)
          positivity
        · change (0 : ℝ) < 6*e*(2*e+1)/(1+3*e+7*e^2)
          positivity
        · change (0 : ℝ) < 9*e*(3*e+1)/(1+3*e+7*e^2)
          positivity
        · change (0 : ℝ) < 6/(1+3*e+7*e^2)
          positivity
    exact ⟨hs.le, iff_of_false (ne_of_gt hs) hi⟩

private lemma point_geometry (e : ℝ) (he : 0 < e) (he4 : e < 1/4)
    (p : Fin 5) :
    pt e p ∈ ({x : Fin 2 → ℝ | ∀ i, row (nodes e) x i ≤ 1}).extremePoints ℝ ∧
    active (nodes e) (pt e p) = roots p := by
  classical
  have hfeas : ∀ i, row (nodes e) (pt e p) i ≤ 1 := by
    intro i
    have ht := slack_table e he he4 p i
    have hs := (slack_spec e he he4 p i).1
    linarith
  have hact : active (nodes e) (pt e p) = roots p := by
    ext i
    rw [mem_active]
    have ht := slack_table e he he4 p i
    have hs := (slack_spec e he he4 p i).2
    constructor
    · intro h
      apply hs.mp
      linarith
    · intro h
      have hz := hs.mpr h
      linarith
  have hc : (roots p).card = 2 := by fin_cases p <;> decide
  exact ⟨(extreme_iff_tight_card (nodes e) (nodes_injective e he he4)
    (by norm_num : 2 < 6) (pt e p)).mpr ⟨hfeas, by rw [hact,hc]⟩,hact⟩

private lemma different_points (e : ℝ) (he : 0 < e) (he4 : e < 1/4)
    (p q : Fin 5) (hpq : p ≠ q) : pt e p ≠ pt e q := by
  intro h
  have hset := congrArg (active (nodes e)) h
  rw [(point_geometry e he he4 p).2, (point_geometry e he he4 q).2] at hset
  have hinj : Function.Injective roots := by decide
  exact hpq (hinj hset)

private lemma edge_slice (e : ℝ) (he : 0 < e) (he4 : e < 1/4)
    (p q : Fin 5) (hc : (roots p ∩ roots q).card + 1 = 2) :
    IsExposed ℝ {x : Fin 2 → ℝ | ∀ i, row (nodes e) x i ≤ 1}
      (segment ℝ (pt e p) (pt e q)) ∧
    {x : Fin 2 → ℝ | (∀ i, row (nodes e) x i ≤ 1) ∧
      ∀ i ∈ roots p ∩ roots q, row (nodes e) x i = 1} =
        segment ℝ (pt e p) (pt e q) := by
  have hp := point_geometry e he he4 p
  have hq := point_geometry e he he4 q
  have hpc := ((extreme_iff_tight_card (nodes e) (nodes_injective e he he4)
    (by norm_num : 2 < 6) (pt e p)).mp hp.1).2
  have hqc := ((extreme_iff_tight_card (nodes e) (nodes_injective e he he4)
    (by norm_num : 2 < 6) (pt e q)).mp hq.1).2
  have hcommon : (active (nodes e) (pt e p) ∩ active (nodes e) (pt e q)).card+1=2 := by
    rw [hp.2,hq.2]
    exact hc
  refine ⟨exposed_edge (nodes e) (nodes_injective e he he4) (by norm_num)
    (pt e p) (pt e q) hp.1.1 hq.1.1 hpc hqc hcommon, ?_⟩
  simpa only [hp.2,hq.2] using common_slice_eq_segment (nodes e)
    (nodes_injective e he he4) (by norm_num : 2 < 6)
    (pt e p) (pt e q) hp.1.1 hq.1.1 hpc hqc hcommon

private lemma extreme_segment_endpoints (P : Set (Fin 2 → ℝ))
    (u v z : Fin 2 → ℝ) (hu : u ∈ P) (hv : v ∈ P)
    (hz : z ∈ P.extremePoints ℝ) (hs : z ∈ segment ℝ u v) : z=u ∨ z=v := by
  obtain ⟨s,t,hs,ht,hst,he⟩ := hs
  by_cases hs0 : s=0
  · have ht1 : t=1 := by linarith
    right
    simpa only [hs0,ht1,zero_smul,one_smul,zero_add] using he.symm
  · by_cases ht0 : t=0
    · have hs1 : s=1 := by linarith
      left
      simpa only [ht0,hs1,zero_smul,one_smul,add_zero] using he.symm
    · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      exact Or.inl (hz.2 hu hv ⟨s,t,hspos,htpos,hst,he⟩).symm

/-- The two explicit edge directions span every displacement with coefficients
read from the two ORIGINAL source slacks. -/
private lemma displacement (e : ℝ) (he : 0 < e) (he4 : e < 1/4)
    (z : Fin 2 → ℝ) :
    z-pt e 0 =
      ((1-row (nodes e) z 3)/(6*e^2/(1+4*e^2))) • (pt e 1-pt e 0) +
      ((1-row (nodes e) z 2)/(6*e^2/(1+10*e^2))) • (pt e 2-pt e 0) := by
  have hD : 0 < 1+4*e^2 := by positivity
  have hE : 0 < 1+10*e^2 := by positivity
  rw [row_formula, row_formula]
  funext j
  fin_cases j
  · change z 0 - 9*e/(1+4*e^2) =
      ((1-((2*e-e)*z 0+((2*e)^2-(1+7*e^2)/3)*z 1))/(6*e^2/(1+4*e^2))) *
        (3*e/(1+4*e^2)-9*e/(1+4*e^2)) +
      ((1-((e-e)*z 0+(e^2-(1+7*e^2)/3)*z 1))/(6*e^2/(1+10*e^2))) *
        (15*e/(1+10*e^2)-9*e/(1+4*e^2))
    field_simp [ne_of_gt he,ne_of_gt hD,ne_of_gt hE] <;> ring
  · change z 1 - (-3/(1+4*e^2)) =
      ((1-((2*e-e)*z 0+((2*e)^2-(1+7*e^2)/3)*z 1))/(6*e^2/(1+4*e^2))) *
        (-3/(1+4*e^2)-(-3/(1+4*e^2))) +
      ((1-((e-e)*z 0+(e^2-(1+7*e^2)/3)*z 1))/(6*e^2/(1+10*e^2))) *
        (-3/(1+10*e^2)-(-3/(1+4*e^2)))
    field_simp [ne_of_gt he,ne_of_gt hD,ne_of_gt hE] <;> ring

/-- Completeness: there are exactly these two exposed original-edge neighbors.
No vertex or adjacency catalogue is supplied. -/
theorem neighbors (e : ℝ) (he : 0 < e) (he4 : e < 1/4) (z : Fin 2 → ℝ) :
    (z ∈ ({x : Fin 2 → ℝ | ∀ i, row (nodes e) x i ≤ 1}).extremePoints ℝ ∧
      z ≠ pt e 0 ∧ IsExposed ℝ {x : Fin 2 → ℝ | ∀ i, row (nodes e) x i ≤ 1}
        (segment ℝ (pt e 0) z)) ↔ z=pt e 1 ∨ z=pt e 2 := by
  classical
  let P : Set (Fin 2 → ℝ) := {x | ∀ i, row (nodes e) x i ≤ 1}
  have hu := (point_geometry e he he4 0).1
  have hl := (point_geometry e he he4 1).1
  have hr := (point_geometry e he he4 2).1
  have el := edge_slice e he he4 0 1 (by decide)
  have er := edge_slice e he he4 0 2 (by decide)
  constructor
  · rintro ⟨hz,hzu,hexp⟩
    by_cases h2 : row (nodes e) z 2=1
    · have hmem : z ∈ segment ℝ (pt e 0) (pt e 1) := by
        rw [← el.2]
        refine ⟨hz.1,?_⟩
        intro i hi
        have hi2 : i=2 := by
          have hset : roots 0 ∩ roots 1 = {(2 : Fin 6)} := by decide
          rw [hset] at hi
          exact Finset.mem_singleton.mp hi
        simpa only [hi2] using h2
      rcases extreme_segment_endpoints P (pt e 0) (pt e 1) z hu.1 hl.1 hz hmem with h | h
      · exact False.elim (hzu h)
      · exact Or.inl h
    · by_cases h3 : row (nodes e) z 3=1
      · have hmem : z ∈ segment ℝ (pt e 0) (pt e 2) := by
          rw [← er.2]
          refine ⟨hz.1,?_⟩
          intro i hi
          have hi3 : i=3 := by
            have hset : roots 0 ∩ roots 2 = {(3 : Fin 6)} := by decide
            rw [hset] at hi
            exact Finset.mem_singleton.mp hi
          simpa only [hi3] using h3
        rcases extreme_segment_endpoints P (pt e 0) (pt e 2) z hu.1 hr.1 hz hmem with h | h
        · exact False.elim (hzu h)
        · exact Or.inr h
      · have humem : pt e 0 ∈ segment ℝ (pt e 0) z :=
          ⟨1,0,by norm_num,by norm_num,by norm_num,by simp⟩
        have hzmem : z ∈ segment ℝ (pt e 0) z :=
          ⟨0,1,by norm_num,by norm_num,by norm_num,by simp⟩
        obtain ⟨f,hf⟩ := hexp ⟨pt e 0,humem⟩
        rw [hf] at humem hzmem
        have hLe : f (pt e 1) ≤ f (pt e 0) := humem.2 (pt e 1) hl.1
        have hRe : f (pt e 2) ≤ f (pt e 0) := humem.2 (pt e 2) hr.1
        have hzeq : f z=f (pt e 0) := le_antisymm
          (humem.2 z hz.1) (hzmem.2 (pt e 0) hu.1)
        have htl : 0 < 6*e^2/(1+4*e^2) := by positivity
        have htr : 0 < 6*e^2/(1+10*e^2) := by positivity
        have hbl : 0 < (1-row (nodes e) z 3)/(6*e^2/(1+4*e^2)) :=
          div_pos (sub_pos.mpr (lt_of_le_of_ne (hz.1 3) h3)) htl
        have hbr : 0 < (1-row (nodes e) z 2)/(6*e^2/(1+10*e^2)) :=
          div_pos (sub_pos.mpr (lt_of_le_of_ne (hz.1 2) h2)) htr
        have hd := congrArg f (displacement e he he4 z)
        simp only [map_sub,map_add,map_smul,smul_eq_mul] at hd
        rw [hzeq,sub_self] at hd
        have hnon := mul_nonpos_of_nonneg_of_nonpos hbr.le (sub_nonpos.mpr hRe)
        have hLeq : f (pt e 1)=f (pt e 0) := by
          apply le_antisymm hLe
          by_contra hn
          have hp := mul_neg_of_pos_of_neg hbl
            (sub_neg.mpr (lt_of_not_ge hn))
          linarith
        have hlseg : pt e 1 ∈ segment ℝ (pt e 0) z := by
          rw [hf]
          refine ⟨hl.1,?_⟩
          intro y hy
          rw [hLeq]
          exact humem.2 y hy
        rcases extreme_segment_endpoints P (pt e 0) z (pt e 1) hu.1 hz.1 hl hlseg with h | h
        · exact False.elim (different_points e he he4 1 0 (by decide) h)
        · have hL2 : row (nodes e) (pt e 1) 2=1 := by
            apply (mem_active (nodes e) (pt e 1) 2).mp
            rw [(point_geometry e he he4 1).2]
            decide
          exact False.elim (h2 (h ▸ hL2))
  · rintro (rfl | rfl)
    · exact ⟨hl,different_points e he he4 1 0 (by decide),el.1⟩
    · exact ⟨hr,different_points e he he4 2 0 (by decide),er.1⟩

private def score (e : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  row (nodes e) x 0 + row (nodes e) x 5

private lemma score_formula (e : ℝ) (x : Fin 2 → ℝ) :
    score e x = (-2*e)*x 0 + ((4-14*e^2)/3)*x 1 := by
  unfold score
  rw [row_formula, row_formula]
  change ((-1-e)*x 0+(((-1 : ℝ)^2-(1+7*e^2)/3)*x 1)) +
    ((1-e)*x 0+(((1 : ℝ)^2-(1+7*e^2)/3)*x 1)) =
      (-2*e)*x 0+((4-14*e^2)/3)*x 1
  ring

private lemma score_values (e : ℝ) (he : 0 < e) (he4 : e < 1/4) :
    score e (pt e 3)-score e (pt e 0) = 6*(1+2*e^2)/(1+4*e^2) ∧
    score e (pt e 1)-score e (pt e 0) = 12*e^2/(1+4*e^2) ∧
    score e (pt e 2)-score e (pt e 0) =
      12*e^2*(1-2*e^2)/((1+4*e^2)*(1+10*e^2)) := by
  obtain ⟨he2,h1,h2,h3,hD,hE,hF,hG⟩ := parameter_bounds e he he4
  have hF' : (2 - e^2*7 : ℝ) ≠ 0 := by nlinarith
  simp_rw [score_formula]
  change ((-2*e)*(0)+((4-14*e^2)/3)*(3/(2-7*e^2))) -
      ((-2*e)*(9*e/(1+4*e^2))+((4-14*e^2)/3)*(-3/(1+4*e^2))) = 6*(1+2*e^2)/(1+4*e^2) ∧
    ((-2*e)*(3*e/(1+4*e^2))+((4-14*e^2)/3)*(-3/(1+4*e^2))) -
      ((-2*e)*(9*e/(1+4*e^2))+((4-14*e^2)/3)*(-3/(1+4*e^2))) = 12*e^2/(1+4*e^2) ∧
    ((-2*e)*(15*e/(1+10*e^2))+((4-14*e^2)/3)*(-3/(1+10*e^2))) -
      ((-2*e)*(9*e/(1+4*e^2))+((4-14*e^2)/3)*(-3/(1+4*e^2))) =
        12*e^2*(1-2*e^2)/((1+4*e^2)*(1+10*e^2))
  constructor
  · field_simp [ne_of_gt hD,ne_of_gt hF,hF'] <;> ring
  · constructor <;> field_simp [ne_of_gt hD,ne_of_gt hE] <;> ring

/-- Both actual neighbor gains, not only a weighted lower guarantee, are small. -/
theorem gain_bounds (e : ℝ) (he : 0 < e) (he4 : e < 1/4) :
    0 < score e (pt e 3)-score e (pt e 0) ∧
    (0 < score e (pt e 1)-score e (pt e 0) ∧
      score e (pt e 1)-score e (pt e 0) <
        2*e^2*(score e (pt e 3)-score e (pt e 0))) ∧
    (0 < score e (pt e 2)-score e (pt e 0) ∧
      score e (pt e 2)-score e (pt e 0) <
        2*e^2*(score e (pt e 3)-score e (pt e 0))) := by
  obtain ⟨he2,h1,h2,h3,hD,hE,hF,hG⟩ := parameter_bounds e he he4
  obtain ⟨hg,hL,hR⟩ := score_values e he he4
  have hgpos : 0 < score e (pt e 3)-score e (pt e 0) := by rw [hg]; positivity
  have heSq : 0 < e^2 := sq_pos_of_pos he
  have hn : 0 < 1-2*e^2 := by nlinarith
  refine ⟨hgpos,?_,?_⟩
  · rw [hL,hg]
    constructor
    · positivity
    · apply (div_lt_iff₀ hD).mpr
      have hid : (2*e^2*(6*(1+2*e^2)/(1+4*e^2)))*(1+4*e^2) =
          12*e^2*(1+2*e^2) := by
        field_simp [ne_of_gt hD]
        <;> ring
      rw [hid]
      have hh := mul_lt_mul_of_pos_left (show (1 : ℝ) < 1+2*e^2 by nlinarith)
        (show 0 < 12*e^2 by positivity)
      simpa only [mul_one] using hh
  · rw [hR,hg]
    constructor
    · positivity
    · apply (div_lt_iff₀ (mul_pos hD hE)).mpr
      have hid : (2*e^2*(6*(1+2*e^2)/(1+4*e^2)))*
          ((1+4*e^2)*(1+10*e^2)) = 12*e^2*(1+2*e^2)*(1+10*e^2) := by
        field_simp [ne_of_gt hD]
        <;> ring
      rw [hid]
      have hprod : (1-2*e^2) < (1+2*e^2)*(1+10*e^2) := by nlinarith [sq_nonneg (e^2)]
      simpa only [mul_assoc] using
        mul_lt_mul_of_pos_left hprod (show 0 < 12*e^2 by positivity)

/-- Three actual original edges still suffice on every member of the family. -/
theorem three_edge_route (e : ℝ) (he : 0 < e) (he4 : e < 1/4) :
    ∃ r : Fin 4 → (Fin 2 → ℝ), r 0=pt e 0 ∧ r 3=pt e 3 ∧
      (∀ i, r i ∈ ({x : Fin 2 → ℝ | ∀ j, row (nodes e) x j ≤ 1}).extremePoints ℝ) ∧
      ∀ i : Fin 3, r i.castSucc ≠ r i.succ ∧
        IsExposed ℝ {x : Fin 2 → ℝ | ∀ j, row (nodes e) x j ≤ 1}
          (segment ℝ (r i.castSucc) (r i.succ)) := by
  let r : Fin 4 → (Fin 2 → ℝ) := ![pt e 0,pt e 1,pt e 4,pt e 3]
  refine ⟨r,rfl,rfl,?_,?_⟩
  · intro i
    fin_cases i
    · exact (point_geometry e he he4 0).1
    · exact (point_geometry e he he4 1).1
    · exact (point_geometry e he he4 4).1
    · exact (point_geometry e he he4 3).1
  · intro i
    fin_cases i
    · exact ⟨different_points e he he4 0 1 (by decide),
        (edge_slice e he he4 0 1 (by decide)).1⟩
    · exact ⟨different_points e he he4 1 4 (by decide),
        (edge_slice e he he4 1 4 (by decide)).1⟩
    · exact ⟨different_points e he he4 4 3 (by decide),
        (edge_slice e he he4 4 3 (by decide)).1⟩

end Hirsch.SmallGain

/-- Even the BEST incident original edge can make an arbitrarily small relative
target-score gain at fixed dimension two and six original rows. Nevertheless a
three-edge original route is constructed. This is not a diameter lower bound. -/
theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : ℝ, 0 < e ∧ e < 1/4 ∧
      let a : Fin 6 → ℝ := ![-1,0,e,2*e,3*e,1]
      let u : Fin 2 → ℝ := ![9*e/(1+4*e^2),-3/(1+4*e^2)]
      let l : Fin 2 → ℝ := ![3*e/(1+4*e^2),-3/(1+4*e^2)]
      let r : Fin 2 → ℝ := ![15*e/(1+10*e^2),-3/(1+10*e^2)]
      let v : Fin 2 → ℝ := ![0,3/(2-7*e^2)]
      let A : (Fin 2 → ℝ) → Fin 6 → ℝ := fun x i =>
        ∑ j : Fin 2, (a i ^ (j.val+1) - (∑ k, a k ^ (j.val+1))/(6 : ℝ))*x j
      let P : Set (Fin 2 → ℝ) := {x | ∀ i, A x i ≤ 1}
      let f : (Fin 2 → ℝ) → ℝ := fun x => A x 0 + A x 5
      u ∈ P.extremePoints ℝ ∧ v ∈ P.extremePoints ℝ ∧ u ≠ v ∧
      0 < f v-f u ∧ l ≠ r ∧
      (∀ z : Fin 2 → ℝ,
        (z ∈ P.extremePoints ℝ ∧ z ≠ u ∧ IsExposed ℝ P (segment ℝ u z)) ↔ z=l ∨ z=r) ∧
      (∀ z : Fin 2 → ℝ,
        (z ∈ P.extremePoints ℝ ∧ z ≠ u ∧ IsExposed ℝ P (segment ℝ u z)) →
          0 < f z-f u ∧ f z-f u < δ*(f v-f u)) ∧
      ∃ path : Fin 4 → (Fin 2 → ℝ), path 0=u ∧ path 3=v ∧
        (∀ i, path i ∈ P.extremePoints ℝ) ∧
        ∀ i : Fin 3, path i.castSucc ≠ path i.succ ∧
          IsExposed ℝ P (segment ℝ (path i.castSucc) (path i.succ)) := by
  classical
  let e : ℝ := min (1/8) (δ/4)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he8 : e ≤ 1/8 := min_le_left _ _
  have heδ : e ≤ δ/4 := min_le_right _ _
  have he4 : e < 1/4 := by linarith
  have heSmall : 2*e^2 < δ := by
    have hp : 0 ≤ e*(1/8-e) := mul_nonneg he.le (sub_nonneg.mpr he8)
    nlinarith
  have hg := Hirsch.SmallGain.gain_bounds e he he4
  refine ⟨e,he,he4,(Hirsch.SmallGain.point_geometry e he he4 0).1,
    (Hirsch.SmallGain.point_geometry e he he4 3).1,
    Hirsch.SmallGain.different_points e he he4 0 3 (by decide),hg.1,
    Hirsch.SmallGain.different_points e he he4 1 2 (by decide),
    Hirsch.SmallGain.neighbors e he he4,?_,Hirsch.SmallGain.three_edge_route e he he4⟩
  intro z hz
  have hb := mul_lt_mul_of_pos_right heSmall hg.1
  rcases (Hirsch.SmallGain.neighbors e he he4 z).mp hz with rfl | rfl
  · exact ⟨hg.2.1.1,hg.2.1.2.trans hb⟩
  · exact ⟨hg.2.2.1,hg.2.2.2.trans hb⟩

#print axioms Hirsch.SmallGain.point_geometry
#print axioms Hirsch.SmallGain.neighbors
#print axioms Hirsch.SmallGain.gain_bounds
#print axioms Hirsch.SmallGain.three_edge_route
#print axioms solution
