-- Prove2me | solution 1 for Hirsch.moment_common_rows_expose_edges
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-17T17:03:47.198998+00:00
-- url     : https://prove2.me/submissions/27db3c8f-ba4b-4b18-8740-dc9f979266dc

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

/-- Constructive ordinary-edge criterion for the ORIGINAL moment inequalities.
No vertex, independence, supporting-functional, or adjacency oracle is assumed. -/
theorem solution (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d,
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let I : Finset (Fin m) := Finset.univ.filter (fun i => row u i = 1)
    let J : Finset (Fin m) := Finset.univ.filter (fun i => row v i = 1)
    (∀ i, row u i ≤ 1) → (∀ i, row v i ≤ 1) →
    I.card = d → J.card = d → (I ∩ J).card + 1 = d →
      u ≠ v ∧ u ∈ P.extremePoints ℝ ∧ v ∈ P.extremePoints ℝ ∧
      {z | z ∈ P ∧ ∀ i ∈ I ∩ J, row z i = 1} = segment ℝ u v ∧
      (∀ z ∈ P, (∑ i ∈ I ∩ J, row z i) ≤ ((I ∩ J).card : ℝ) ∧
        ((∑ i ∈ I ∩ J, row z i) = ((I ∩ J).card : ℝ) ↔ z ∈ segment ℝ u v)) ∧
      IsExposed ℝ P (segment ℝ u v) ∧ IsExtreme ℝ P (segment ℝ u v) ∧
      (∀ t : ℝ, 0 < t → t < 1 →
        (Finset.univ.filter (fun i => row ((1-t) • u + t • v) i = 1)) = I ∩ J) := by
  classical
  dsimp only
  intro hu hv huc hvc hc
  change (Hirsch.MomentVertices.active a u).card = d at huc
  change (Hirsch.MomentVertices.active a v).card = d at hvc
  change (Hirsch.MomentVertices.active a u ∩ Hirsch.MomentVertices.active a v).card + 1 = d at hc
  have heq := Hirsch.MomentEdges.common_slice_eq_segment a ha hm u v hu hv huc hvc hc
  have hex := Hirsch.MomentEdges.exposed_edge a ha hm u v hu hv huc hvc hc
  refine ⟨?_, (Hirsch.MomentVertices.extreme_iff_tight_card a ha hm u).mpr ⟨hu,huc⟩,
    (Hirsch.MomentVertices.extreme_iff_tight_card a ha hm v).mpr ⟨hv,hvc⟩,
    heq, ?_, hex, hex.isExtreme, ?_⟩
  · intro huv
    subst v
    simp only [Finset.inter_self, huc] at hc
    omega
  · intro z hz
    refine ⟨Hirsch.MomentEdges.sum_rows_le a _ z hz, ?_⟩
    change (∑ i ∈ Hirsch.MomentVertices.active a u ∩ Hirsch.MomentVertices.active a v,
      Hirsch.MomentBarycentric.row a z i) =
        ((Hirsch.MomentVertices.active a u ∩ Hirsch.MomentVertices.active a v).card : ℝ) ↔
      z ∈ segment ℝ u v
    rw [Hirsch.MomentEdges.sum_rows_eq_iff a
      (Hirsch.MomentVertices.active a u ∩ Hirsch.MomentVertices.active a v) z hz, ← heq]
    exact ⟨fun h => ⟨hz,h⟩, fun h => h.2⟩
  · intro t ht ht1
    exact Hirsch.MomentEdges.interior_tight_rows a u v hu hv t ht ht1

#print axioms Hirsch.MomentEdges.common_is_erase
#print axioms Hirsch.MomentEdges.common_slice_eq_segment
#print axioms Hirsch.MomentEdges.interior_tight_rows
#print axioms Hirsch.MomentEdges.exposed_edge
#print axioms solution
