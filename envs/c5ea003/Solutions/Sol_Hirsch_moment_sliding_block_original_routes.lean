-- Prove2me | solution 1 for Hirsch.moment_sliding_block_original_routes
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-17T20:10:42.945168+00:00
-- url     : https://prove2.me/submissions/7ccdf32a-8620-48dd-880b-595615703cfb

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

namespace Hirsch.MomentCorridor

open Set MomentBarycentric MomentVertices MomentEdges

/-- Consecutive roots are grouped in pairs; the degree is the ambient dimension. -/
noncomputable def roots (a : ℕ → ℝ) (k s : ℕ) : Polynomial ℝ :=
  ∏ j : Fin k,
    (Polynomial.X - Polynomial.C (a (s + 2*j.val))) *
      (Polynomial.X - Polynomial.C (a (s + 2*j.val + 1)))

lemma eval_roots (a : ℕ → ℝ) (k s : ℕ) (t : ℝ) :
    (roots a k s).eval t =
      ∏ j : Fin k, (t-a (s+2*j.val)) * (t-a (s+2*j.val+1)) := by
  simp [roots, Polynomial.eval_prod]

lemma degree_roots (a : ℕ → ℝ) (k s : ℕ) :
    (roots a k s).natDegree = 2*k := by
  classical
  unfold roots
  rw [Polynomial.natDegree_prod_of_monic Finset.univ
    (fun j : Fin k => (Polynomial.X - Polynomial.C (a (s+2*j.val))) *
      (Polynomial.X - Polynomial.C (a (s+2*j.val+1))))
    (fun j _ => (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _))]
  have hd : ∀ j : Fin k,
      ((Polynomial.X - Polynomial.C (a (s+2*j.val))) *
        (Polynomial.X - Polynomial.C (a (s+2*j.val+1))) : Polynomial ℝ).natDegree = 2 := by
    intro j
    rw [(Polynomial.monic_X_sub_C _).natDegree_mul (Polynomial.monic_X_sub_C _)]
    simp
  simp_rw [hd]
  simp [Nat.mul_comm]

lemma roots_nonneg (a : ℕ → ℝ) (ha : StrictMono a) (k s i : ℕ) :
    0 ≤ (roots a k s).eval (a i) := by
  rw [eval_roots]
  apply Finset.prod_nonneg
  intro j _
  by_cases hi : i ≤ s+2*j.val
  · apply mul_nonneg_of_nonpos_of_nonpos
    · exact sub_nonpos.mpr (ha.monotone hi)
    · exact sub_nonpos.mpr (ha.monotone (by omega))
  · apply mul_nonneg
    · exact sub_nonneg.mpr (ha.monotone (by omega))
    · exact sub_nonneg.mpr (ha.monotone (by omega))

lemma roots_zero_iff (a : ℕ → ℝ) (ha : StrictMono a) (k s i : ℕ) :
    (roots a k s).eval (a i) = 0 ↔ s ≤ i ∧ i < s+2*k := by
  classical
  rw [eval_roots]
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp h
    have hjb := j.isLt
    rcases mul_eq_zero.mp hj with h | h
    · have he := ha.injective (sub_eq_zero.mp h)
      omega
    · have he := ha.injective (sub_eq_zero.mp h)
      omega
  · rintro ⟨hsi, his⟩
    let j : Fin k := ⟨(i-s)/2, by omega⟩
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    have hpar : (i-s)%2 = 0 ∨ (i-s)%2 = 1 := by omega
    rcases hpar with h | h
    · have he : i = s+2*j.val := by dsimp [j]; omega
      rw [he, sub_self, zero_mul]
    · have he : i = s+2*j.val+1 := by dsimp [j]; omega
      rw [he, sub_self, mul_zero]

noncomputable def mean (a : ℕ → ℝ) (k m s : ℕ) : ℝ :=
  (∑ i : Fin m, (roots a k s).eval (a i.val)) / (m : ℝ)

lemma mean_pos (a : ℕ → ℝ) (ha : StrictMono a) (k m s : ℕ)
    (hm : 2*k < m) : 0 < mean a k m s := by
  obtain ⟨i, hi⟩ : ∃ i : Fin m, ¬ (s ≤ i.val ∧ i.val < s+2*k) := by
    by_cases hs : s = 0
    · refine ⟨⟨2*k, hm⟩, ?_⟩
      dsimp only
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      dsimp only
      omega
  have hne : (roots a k s).eval (a i.val) ≠ 0 :=
    fun h => hi ((roots_zero_iff a ha k s i.val).mp h)
  have hp : 0 < (roots a k s).eval (a i.val) :=
    lt_of_le_of_ne (roots_nonneg a ha k s i.val) hne.symm
  have hsum : 0 < ∑ i : Fin m, (roots a k s).eval (a i.val) :=
    hp.trans_le (Finset.single_le_sum
      (fun j _ => roots_nonneg a ha k s j.val) (Finset.mem_univ i))
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact div_pos hsum hmR

/-- The point is given by coefficients, not selected from a feasible-set oracle. -/
noncomputable def point (a : ℕ → ℝ) (k m s : ℕ) : Fin (2*k) → ℝ :=
  fun j => (-(mean a k m s)⁻¹) * (roots a k s).coeff (j.val+1)

lemma point_identity (a : ℕ → ℝ) (ha : StrictMono a) (k m s : ℕ)
    (hm : 2*k < m) (i : Fin m) :
    row (fun j : Fin m => a j.val) (point a k m s) i =
      1 - (roots a k s).eval (a i.val) / mean a k m s := by
  have hh0 := ne_of_gt (mean_pos a ha k m s hm)
  have hm0 : (Fintype.card (Fin m) : ℝ) ≠ 0 := by
    simp only [Fintype.card_fin]
    exact ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  calc
    row (fun j : Fin m => a j.val) (point a k m s) i =
      (-(mean a k m s)⁻¹) *
        ∑ j : Fin (2*k),
          (a i.val ^ (j.val+1) -
            (∑ l : Fin m, a l.val ^ (j.val+1)) / (m : ℝ)) *
              (roots a k s).coeff (j.val+1) := by
      unfold row point
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (-(mean a k m s)⁻¹) *
      ((roots a k s).eval (a i.val) - mean a k m s) := by
      congr 1
      simpa only [Fintype.card_fin, mean] using
        MomentSmallFaces.centered_eval (fun j : Fin m => a j.val)
          (roots a k s) (2*k) (by rw [degree_roots]) hm0 i
    _ = 1 - (roots a k s).eval (a i.val) / mean a k m s := by
      field_simp [hh0]
      <;> ring

lemma point_feasible (a : ℕ → ℝ) (ha : StrictMono a) (k m s : ℕ)
    (hm : 2*k < m) :
    ∀ i : Fin m, row (fun j : Fin m => a j.val) (point a k m s) i ≤ 1 := by
  intro i
  rw [point_identity a ha k m s hm]
  have hquot := div_nonneg (roots_nonneg a ha k s i.val) (mean_pos a ha k m s hm).le
  linarith

lemma point_tight (a : ℕ → ℝ) (ha : StrictMono a) (k m s : ℕ)
    (hm : 2*k < m) (i : Fin m) :
    row (fun j : Fin m => a j.val) (point a k m s) i = 1 ↔
      s ≤ i.val ∧ i.val < s+2*k := by
  rw [point_identity a ha k m s hm]
  have hh0 := ne_of_gt (mean_pos a ha k m s hm)
  constructor
  · intro he
    have hquot : (roots a k s).eval (a i.val) / mean a k m s = 0 := by linarith
    have hz := div_mul_cancel₀ ((roots a k s).eval (a i.val)) hh0
    rw [hquot, zero_mul] at hz
    exact (roots_zero_iff a ha k s i.val).mp hz.symm
  · intro hi
    rw [(roots_zero_iff a ha k s i.val).mpr hi, zero_div, sub_zero]

noncomputable def block (d m s : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => s ≤ i.val ∧ i.val < s+d)

lemma mem_block (d m s : ℕ) (i : Fin m) :
    i ∈ block d m s ↔ s ≤ i.val ∧ i.val < s+d := by
  simp [block]

lemma card_block (d m s : ℕ) (hs : s+d ≤ m) : (block d m s).card = d := by
  classical
  let f : Fin d → Fin m := fun j => ⟨s+j.val, by have hj := j.isLt; omega⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    dsimp only [f] at hval
    omega
  have heq : block d m s = Finset.univ.image f := by
    ext i
    simp only [mem_block, Finset.mem_image]
    constructor
    · rintro ⟨hsi, hi⟩
      refine ⟨⟨i.val-s, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp only [f]
      omega
    · rintro ⟨j, _, h⟩
      have hval := congrArg Fin.val h
      have hj := j.isLt
      dsimp only [f] at hval
      constructor <;> omega
  have hc : (Finset.univ.image f).card = (Finset.univ : Finset (Fin d)).card :=
    Finset.card_image_iff.mpr hf.injOn
  rw [heq, hc]
  simp

lemma point_active (a : ℕ → ℝ) (ha : StrictMono a) (k m s : ℕ)
    (hm : 2*k < m) :
    active (fun j : Fin m => a j.val) (point a k m s) = block (2*k) m s := by
  ext i
  rw [mem_active, mem_block, point_tight a ha k m s hm]

lemma restricted_injective (a : ℕ → ℝ) (ha : StrictMono a) (m : ℕ) :
    Function.Injective (fun i : Fin m => a i.val) := by
  intro i j h
  exact Fin.ext (ha.injective h)

lemma point_extreme (a : ℕ → ℝ) (ha : StrictMono a) (k m s : ℕ)
    (hm : 2*k < m) (hs : s+2*k ≤ m) :
    point a k m s ∈
      ({x : Fin (2*k) → ℝ | ∀ i : Fin m, row (fun j : Fin m => a j.val) x i ≤ 1}).extremePoints ℝ := by
  apply (extreme_iff_tight_card _ (restricted_injective a ha m) hm _).mpr
  refine ⟨point_feasible a ha k m s hm, ?_⟩
  rw [point_active a ha k m s hm]
  exact card_block (2*k) m s hs

lemma overlap_card (k m s : ℕ) (hk : 0 < k) (hs : s+1+2*k ≤ m) :
    ((block (2*k) m s) ∩ block (2*k) m (s+1)).card + 1 = 2*k := by
  classical
  let r : Fin m := ⟨s, by omega⟩
  have hr : r ∈ block (2*k) m s := by
    rw [mem_block]
    dsimp only [r]
    constructor <;> omega
  have heq : (block (2*k) m s) ∩ block (2*k) m (s+1) =
      (block (2*k) m s).erase r := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      obtain ⟨hleft, hright⟩ := Finset.mem_inter.mp hi
      have hnext := (mem_block (2*k) m (s+1) i).mp hright
      apply Finset.mem_erase.mpr
      refine ⟨?_, hleft⟩
      intro hir
      have hval : i.val = s := congrArg Fin.val hir
      omega
    · intro hi
      obtain ⟨hine, hleft⟩ := Finset.mem_erase.mp hi
      have hwin := (mem_block (2*k) m s i).mp hleft
      have hvalne : i.val ≠ s := by
        intro hval
        apply hine
        apply Fin.ext
        exact hval
      apply Finset.mem_inter.mpr
      refine ⟨hleft, (mem_block (2*k) m (s+1) i).mpr ?_⟩
      constructor <;> omega
  rw [heq]
  have hc := Finset.card_erase_add_one hr
  rw [card_block (2*k) m s (by omega)] at hc
  exact hc

lemma point_next_edge (a : ℕ → ℝ) (ha : StrictMono a) (k m s : ℕ)
    (hk : 0 < k) (hm : 2*k < m) (hs : s+1+2*k ≤ m) :
    IsExposed ℝ
      {x : Fin (2*k) → ℝ | ∀ i : Fin m, row (fun j : Fin m => a j.val) x i ≤ 1}
      (segment ℝ (point a k m s) (point a k m (s+1))) := by
  apply exposed_edge _ (restricted_injective a ha m) hm
    (point a k m s) (point a k m (s+1))
    (point_feasible a ha k m s hm) (point_feasible a ha k m (s+1) hm)
  · rw [point_active a ha k m s hm]
    exact card_block (2*k) m s (by omega)
  · rw [point_active a ha k m (s+1) hm]
    exact card_block (2*k) m (s+1) hs
  · rw [point_active a ha k m s hm, point_active a ha k m (s+1) hm]
    exact overlap_card k m s hk hs

lemma point_start_injective (a : ℕ → ℝ) (ha : StrictMono a) (k m r s : ℕ)
    (hk : 0 < k) (hm : 2*k < m) (hr : r+2*k ≤ m) (hs : s+2*k ≤ m)
    (he : point a k m r = point a k m s) : r = s := by
  let ir : Fin m := ⟨r, by omega⟩
  let is : Fin m := ⟨s, by omega⟩
  have hrr : row (fun j : Fin m => a j.val) (point a k m r) ir = 1 :=
    (point_tight a ha k m r hm ir).mpr (by dsimp [ir]; constructor <;> omega)
  have hss : row (fun j : Fin m => a j.val) (point a k m s) is = 1 :=
    (point_tight a ha k m s hm is).mpr (by dsimp [is]; constructor <;> omega)
  rw [he] at hrr
  rw [← he] at hss
  have hsr := ((point_tight a ha k m s hm ir).mp hrr).1
  have hrs := ((point_tight a ha k m r hm is).mp hss).1
  dsimp only [ir, is] at hsr hrs
  omega

/-- A whole explicitly indexed route is constructed, not supplied in a hypothesis. -/
theorem sliding_block_route (k m s L : ℕ) (hk : 0 < k) (hm : 2*k < m)
    (hfit : s+L+2*k ≤ m) (a : ℕ → ℝ) (ha : StrictMono a) :
    L ≤ m-2*k ∧
    ∃ p : Fin (L+1) → (Fin (2*k) → ℝ), Function.Injective p ∧
      (∀ t : Fin (L+1),
        p t ∈ ({x : Fin (2*k) → ℝ | ∀ i : Fin m,
          row (fun j : Fin m => a j.val) x i ≤ 1}).extremePoints ℝ ∧
        (∀ i : Fin m, row (fun j : Fin m => a j.val) (p t) i ≤ 1) ∧
        ∀ i : Fin m, row (fun j : Fin m => a j.val) (p t) i = 1 ↔
          s+t.val ≤ i.val ∧ i.val < s+t.val+2*k) ∧
      (∀ t : Fin L, IsExposed ℝ
        {x : Fin (2*k) → ℝ | ∀ i : Fin m, row (fun j : Fin m => a j.val) x i ≤ 1}
        (segment ℝ (p t.castSucc) (p t.succ))) ∧
      (∀ i : Fin m, ∀ t u v : Fin (L+1), t ≤ u → u ≤ v →
        row (fun j : Fin m => a j.val) (p t) i = 1 →
        row (fun j : Fin m => a j.val) (p v) i = 1 →
        row (fun j : Fin m => a j.val) (p u) i = 1) := by
  let p : Fin (L+1) → (Fin (2*k) → ℝ) := fun t => point a k m (s+t.val)
  refine ⟨by omega, p, ?_, ?_, ?_, ?_⟩
  · intro t u he
    apply Fin.ext
    have ht := t.isLt
    have hu := u.isLt
    have hstarts := point_start_injective a ha k m (s+t.val) (s+u.val)
      hk hm (by omega) (by omega) he
    omega
  · intro t
    have ht := t.isLt
    exact ⟨point_extreme a ha k m (s+t.val) hm (by omega),
      point_feasible a ha k m (s+t.val) hm, point_tight a ha k m (s+t.val) hm⟩
  · intro t
    have ht := t.isLt
    change IsExposed ℝ
      {x : Fin (2*k) → ℝ | ∀ i : Fin m, row (fun j : Fin m => a j.val) x i ≤ 1}
      (segment ℝ (point a k m (s+t.val)) (point a k m (s+(t.val+1))))
    simpa only [Nat.add_assoc] using
      point_next_edge a ha k m (s+t.val) hk hm (by omega)
  · intro i t u v htu huv ht hv
    have ht' := (point_tight a ha k m (s+t.val) hm i).mp ht
    have hv' := (point_tight a ha k m (s+v.val) hm i).mp hv
    apply (point_tight a ha k m (s+u.val) hm i).mpr
    have htu' : t.val ≤ u.val := htu
    have huv' : u.val ≤ v.val := huv
    constructor <;> omega

end Hirsch.MomentCorridor

/-- Sliding consecutive blocks construct an injective original-edge chain with
at most m-2k edges; no vertex list, feasible path, or adjacency oracle is assumed. -/
theorem solution (k m s L : ℕ) (hk : 0 < k) (hm : 2*k < m)
    (hfit : s+L+2*k ≤ m) (a : ℕ → ℝ) (ha : StrictMono a) :
    let row : (Fin (2*k) → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin (2*k),
        (a i.val ^ (j.val+1) - (∑ l : Fin m, a l.val ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin (2*k) → ℝ) := {x | ∀ i : Fin m, row x i ≤ 1}
    L ≤ m-2*k ∧
    ∃ p : Fin (L+1) → (Fin (2*k) → ℝ), Function.Injective p ∧
      (∀ t : Fin (L+1), p t ∈ P.extremePoints ℝ ∧
        (∀ i : Fin m, row (p t) i ≤ 1) ∧
        ∀ i : Fin m, row (p t) i = 1 ↔
          s+t.val ≤ i.val ∧ i.val < s+t.val+2*k) ∧
      (∀ t : Fin L, IsExposed ℝ P (segment ℝ (p t.castSucc) (p t.succ))) ∧
      (∀ i : Fin m, ∀ t u v : Fin (L+1), t ≤ u → u ≤ v →
        row (p t) i = 1 → row (p v) i = 1 → row (p u) i = 1) := by
  exact Hirsch.MomentCorridor.sliding_block_route k m s L hk hm hfit a ha

#print axioms Hirsch.MomentCorridor.roots_zero_iff
#print axioms Hirsch.MomentCorridor.point_extreme
#print axioms Hirsch.MomentCorridor.point_next_edge
#print axioms Hirsch.MomentCorridor.sliding_block_route
#print axioms solution
