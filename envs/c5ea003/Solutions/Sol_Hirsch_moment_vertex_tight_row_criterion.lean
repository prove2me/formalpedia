-- Prove2me | solution 1 for Hirsch.moment_vertex_tight_row_criterion
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-17T10:16:40.550361+00:00
-- url     : https://prove2.me/submissions/64b7b648-b7e7-4bca-a4d6-b4e95138df7a

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

/-- The original moment system has no dependent tight rows, and every actual
vertex is characterized by exactly dimension many tight original inequalities.
Arbitrary active values are explicitly attainable; no rank oracle is a premise. -/
theorem solution (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d,
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    ∀ x : Fin d → ℝ,
      let I : Finset (Fin m) := Finset.univ.filter (fun i => row x i = 1)
      I.card ≤ d ∧
      (∀ values : I → ℝ, ∃ z : Fin d → ℝ, ∀ i : I, row z i.val = values i) ∧
      (x ∈ P.extremePoints ℝ ↔ (∀ i, row x i ≤ 1) ∧ I.card = d) := by
  classical
  dsimp only
  intro x
  refine ⟨Hirsch.MomentVertices.tight_card_le a ha hm x, ?_,
    Hirsch.MomentVertices.extreme_iff_tight_card a ha hm x⟩
  intro values
  obtain ⟨z,hz⟩ := Hirsch.MomentVertices.activeEval_surjective a ha hm x values
  exact ⟨z,fun i => congrFun hz i⟩

#print axioms Hirsch.MomentVertices.tight_card_le
#print axioms Hirsch.MomentVertices.activeEval_surjective
#print axioms Hirsch.MomentVertices.extreme_kernel
#print axioms Hirsch.MomentVertices.extreme_iff_tight_card
#print axioms solution
