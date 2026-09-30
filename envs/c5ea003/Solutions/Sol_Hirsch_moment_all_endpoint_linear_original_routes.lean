-- Prove2me | solution 1 for Hirsch.moment_all_endpoint_linear_original_routes
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-19T00:19:43.162758+00:00
-- url     : https://prove2.me/submissions/aa429b41-0d1b-4b55-ac03-6965bc2a32f3

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

namespace Hirsch.MomentEvenGaps

open MomentRootCatalogue MomentBarycentric

/-- The sign of a nonzero product is the parity of its negative factors. -/
private theorem prod_positive_iff_even_neg {ι : Type*}
    (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, f i ≠ 0) :
    0 < ∏ i ∈ S, f i ↔ (S.filter (fun i => f i < 0)).card % 2 = 0 := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | @insert i S hi ih =>
    intro hf
    have hfi : f i ≠ 0 := hf i (Finset.mem_insert_self i S)
    have hfs : ∀ j ∈ S, f j ≠ 0 :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ S, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfs
    have hnot : i ∉ S.filter (fun j => f j < 0) := by
      intro h
      exact hi (Finset.mem_filter.mp h).1
    by_cases hneg : f i < 0
    · rw [Finset.prod_insert hi, Finset.filter_insert, if_pos hneg,
        Finset.card_insert_of_notMem hnot]
      have hsign : 0 < f i * (∏ j ∈ S, f j) ↔ ¬ 0 < ∏ j ∈ S, f j := by
        constructor
        · intro h hp
          have hn := mul_neg_of_neg_of_pos hneg hp
          linarith
        · intro h
          have hn : (∏ j ∈ S, f j) < 0 :=
            lt_of_le_of_ne (le_of_not_gt h) hprod
          exact mul_pos_of_neg_of_neg hneg hn
      rw [hsign, ih hfs]
      omega
    · have hpos : 0 < f i := lt_of_le_of_ne (le_of_not_gt hneg) hfi.symm
      rw [Finset.prod_insert hi, Finset.filter_insert, if_neg hneg]
      have hsign : 0 < f i * (∏ j ∈ S, f j) ↔ 0 < ∏ j ∈ S, f j := by
        constructor
        · intro h
          by_contra hn
          have hh := mul_nonpos_of_nonneg_of_nonpos hpos.le (le_of_not_gt hn)
          linarith
        · exact mul_pos hpos
      rw [hsign]
      exact ih hfs

/-- Between two nonroots, precisely the intervening roots contribute negative
factors to the product of the two polynomial evaluations. -/
theorem pair_sign_iff_even_gap {m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (S : Finset (Fin m)) (i j : Fin m) (hi : i ∉ S) (hj : j ∉ S) (hij : i < j) :
    0 < (rootPoly a S).eval (a i) * (rootPoly a S).eval (a j) ↔
      (S.filter (fun s => i < s ∧ s < j)).card % 2 = 0 := by
  classical
  let f : Fin m → ℝ := fun s => (a i - a s) * (a j - a s)
  have hnon : ∀ s ∈ S, f s ≠ 0 := by
    intro s hs
    apply mul_ne_zero
    · apply sub_ne_zero.mpr
      intro he
      have h := ha.injective he
      subst s
      exact hi hs
    · apply sub_ne_zero.mpr
      intro he
      have h := ha.injective he
      subst s
      exact hj hs
  have hsign : ∀ s, f s < 0 ↔ i < s ∧ s < j := by
    intro s
    constructor
    · intro hn
      have hab := ha hij
      have hbetween : a i < a s ∧ a s < a j := by
        change (a i - a s) * (a j - a s) < 0 at hn
        rcases mul_neg_iff.mp hn with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
          constructor <;> linarith
      constructor
      · by_contra hh
        have hc := ha.monotone (le_of_not_gt hh)
        linarith [hbetween.1]
      · by_contra hh
        have hc := ha.monotone (le_of_not_gt hh)
        linarith [hbetween.2]
    · rintro ⟨h1,h2⟩
      exact mul_neg_of_neg_of_pos (sub_neg.mpr (ha h1)) (sub_pos.mpr (ha h2))
  have hfilter : S.filter (fun s => f s < 0) =
      S.filter (fun s => i < s ∧ s < j) := by
    apply Finset.filter_congr
    intro s _
    exact hsign s
  rw [eval_rootPoly, eval_rootPoly, ← Finset.prod_mul_distrib]
  exact (prod_positive_iff_even_neg S f hnon).trans (by rw [hfilter])

/-- Normalizing a finite nonzero family by its mean is nonnegative exactly
when all its nonzero entries have the same sign. Either mean sign is allowed. -/
private theorem normalized_iff_pair_products {m : ℕ} (b : Fin m → ℝ)
    (hm : 0 < (m : ℝ)) (hne : ∃ i, b i ≠ 0) :
    let μ : ℝ := (∑ i, b i) / (m : ℝ)
    (μ ≠ 0 ∧ ∀ i, 0 ≤ b i / μ) ↔
      ∀ i, b i ≠ 0 → ∀ j, b j ≠ 0 → 0 < b i * b j := by
  classical
  let μ : ℝ := (∑ i, b i) / (m : ℝ)
  change (μ ≠ 0 ∧ ∀ i, 0 ≤ b i / μ) ↔ _
  constructor
  · rintro ⟨hmu,hpos⟩ i hi j hj
    have hpi : 0 < b i / μ :=
      lt_of_le_of_ne (hpos i) (div_ne_zero hi hmu).symm
    have hpj : 0 < b j / μ :=
      lt_of_le_of_ne (hpos j) (div_ne_zero hj hmu).symm
    have he : b i * b j = ((b i / μ) * (b j / μ)) * μ ^ 2 := by
      field_simp [hmu]
      <;> ring
    rw [he]
    exact mul_pos (mul_pos hpi hpj) (sq_pos_of_ne_zero hmu)
  · intro hprod
    obtain ⟨i₀,hi₀⟩ := hne
    let c : ℝ := b i₀
    have hc : c ≠ 0 := hi₀
    have hnon : ∀ i, 0 ≤ c * b i := by
      intro i
      by_cases hi : b i = 0
      · simp [hi]
      · exact (hprod i₀ hi₀ i hi).le
    have hself : 0 < c * b i₀ := hprod i₀ hi₀ i₀ hi₀
    have hsum : 0 < ∑ i, c * b i :=
      hself.trans_le (Finset.single_le_sum (fun i _ => hnon i) (Finset.mem_univ i₀))
    have hcm : 0 < c * μ := by
      have he : c * μ = (∑ i, c * b i) / (m : ℝ) := by
        rw [← Finset.mul_sum]
        dsimp [μ]
        ring
      rw [he]
      exact div_pos hsum hm
    have hmu : μ ≠ 0 := by
      intro h
      rw [h, mul_zero] at hcm
      exact (lt_irrefl 0) hcm
    refine ⟨hmu,?_⟩
    intro i
    by_cases hi : b i = 0
    · simp [hi]
    · have he : b i / μ = (c * b i) / (c * μ) := by
        field_simp [hc,hmu]
        <;> ring
      rw [he]
      exact (div_pos (hprod i₀ hi₀ i hi) hcm).le

def EvenGaps {m : ℕ} (S : Finset (Fin m)) : Prop :=
  ∀ i ∉ S, ∀ j ∉ S, i < j → (S.filter (fun s => i < s ∧ s < j)).card % 2 = 0

/-- Gale's even-gap condition is EXACTLY the full-label root-polynomial filter,
including the nonzero mean requirement rather than assuming it. -/
theorem root_filter_iff_even_gaps {m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (S : Finset (Fin m)) (hproper : S.card < m) :
    (mean a S ≠ 0 ∧ ∀ i : Fin m, 0 ≤ (rootPoly a S).eval (a i) / mean a S) ↔
      EvenGaps S := by
  classical
  let b : Fin m → ℝ := fun i => (rootPoly a S).eval (a i)
  have hmNat : 0 < m := by omega
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmNat
  obtain ⟨i₀,hi₀⟩ : ∃ i₀ : Fin m, i₀ ∉ S := by
    by_contra hn
    have hall : (Finset.univ : Finset (Fin m)) ⊆ S := by
      intro i _
      by_contra hi
      exact hn ⟨i,hi⟩
    have hc := Finset.card_le_card hall
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    omega
  have hb : ∀ i, b i ≠ 0 ↔ i ∉ S := by
    intro i
    exact not_congr (eval_rootPoly_zero_iff a ha.injective S i)
  have hnorm := normalized_iff_pair_products b hm ⟨i₀,(hb i₀).mpr hi₀⟩
  change (mean a S ≠ 0 ∧ ∀ i, 0 ≤ (rootPoly a S).eval (a i) / mean a S) ↔
    (∀ i, b i ≠ 0 → ∀ j, b j ≠ 0 → 0 < b i * b j) at hnorm
  rw [hnorm]
  constructor
  · intro hp i hi j hj hij
    exact (pair_sign_iff_even_gap a ha S i j hi hj hij).mp
      (hp i ((hb i).mpr hi) j ((hb j).mpr hj))
  · intro hg i hi j hj
    have hiS := (hb i).mp hi
    have hjS := (hb j).mp hj
    rcases lt_trichotomy i j with hij | hij | hji
    · exact (pair_sign_iff_even_gap a ha S i j hiS hjS hij).mpr (hg i hiS j hjS hij)
    · subst j
      simpa only [pow_two] using sq_pos_of_ne_zero hi
    · have hp := (pair_sign_iff_even_gap a ha S j i hjS hiS hji).mpr (hg j hjS i hiS hji)
      simpa only [mul_comm] using hp

noncomputable def parityCatalogue (d m : ℕ) : Finset (Finset (Fin m)) := by
  classical
  exact (Finset.powersetCard d Finset.univ).filter EvenGaps

theorem catalogue_eq_parity {d m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (hm : d < m) : catalogue d a = parityCatalogue d m := by
  classical
  unfold catalogue parityCatalogue
  apply Finset.filter_congr
  intro S hS
  have hcard := (Finset.mem_powersetCard.mp hS).2
  exact root_filter_iff_even_gaps a ha S (by omega)

/-- The accepted numeric catalogue and all its geometric conclusions transfer
to a catalogue using only the ORIGINAL label order and a finite parity test. -/
theorem complete_even_catalogue {d m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (hm : d < m) :
    (∀ S ∈ parityCatalogue d m, mean a S ≠ 0 ∧
      ∀ i : Fin m, 0 ≤ (rootPoly a S).eval (a i) / mean a S) ∧
    Set.InjOn (candidate (d:=d) a) (parityCatalogue d m) ∧
    (∀ x : Fin d → ℝ,
      x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ ↔
        x ∈ (parityCatalogue d m).image (candidate (d:=d) a)) ∧
    (∀ S ∈ parityCatalogue d m, ∀ i : Fin m,
      row a (candidate (d:=d) a S) i = 1 ↔ i ∈ S) ∧
    ((parityCatalogue d m).image (candidate (d:=d) a)).card = (parityCatalogue d m).card ∧
    (parityCatalogue d m).card ≤ Nat.choose m d := by
  classical
  have heq := catalogue_eq_parity a ha hm
  have hold := complete_catalogue a ha.injective hm
  rw [heq] at hold
  refine ⟨?_,hold⟩
  intro S hS
  rw [← heq] at hS
  exact ((mem_catalogue a S).mp hS).2

end Hirsch.MomentEvenGaps

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

namespace Hirsch.AlternatingComplement

/-- A complete order-only configuration, retaining either starting parity. -/
def Legal (m : ℕ) {r : ℕ} (h : Fin r → ℕ) : Prop :=
  StrictMono h ∧ (∀ i, h i < m) ∧
    ∃ b : ℕ, b < 2 ∧ ∀ i, h i % 2 = (b + i.val) % 2

def labels {r : ℕ} (h : Fin r → ℕ) : Finset ℕ :=
  Finset.univ.image h

def Good (m r : ℕ) (H : Finset ℕ) : Prop :=
  ∃ h : Fin r → ℕ, Legal m h ∧ labels h = H

def Exchange (r : ℕ) (S T : Finset ℕ) : Prop :=
  S ≠ T ∧ (S ∩ T).card + 1 = r

lemma exchange_symm {r : ℕ} {S T : Finset ℕ} (h : Exchange r S T) :
    Exchange r T S := by
  exact ⟨Ne.symm h.1, by simpa only [Finset.inter_comm] using h.2⟩

private lemma labels_card {r : ℕ} (h : Fin r → ℕ) (hh : StrictMono h) :
    (labels h).card = r := by
  rw [labels, Finset.card_image_of_injective _ hh.injective]
  simp

private lemma labels_subset {m r : ℕ} (h : Fin r → ℕ)
    (hh : ∀ i, h i < m) : labels h ⊆ Finset.range m := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_range.mpr (hh i)

private lemma lower_bound {r : ℕ} (h : Fin r → ℕ) (hh : StrictMono h)
    (b : ℕ) (hb : b < 2) (hp : ∀ i, h i % 2 = (b + i.val) % 2) :
    ∀ i, b + i.val ≤ h i := by
  have aux : ∀ n : ℕ, ∀ hn : n < r, b + n ≤ h ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      have he := hp ⟨0, hn⟩
      simp only [Fin.val_mk, Nat.add_zero] at he
      omega
    | succ n ih =>
      intro hn
      have hn' : n < r := by omega
      have hlo := ih hn'
      have hidx : (⟨n, hn'⟩ : Fin r) < ⟨n+1, hn⟩ := by
        change n < n+1
        exact Nat.lt_succ_self n
      have hlt : h ⟨n, hn'⟩ < h ⟨n+1, hn⟩ := hh hidx
      omega
  intro i
  exact aux i.val i.isLt

private def packedPrefix {r : ℕ} (b : ℕ) (h : Fin r → ℕ) (t : ℕ) : Fin r → ℕ :=
  fun i => if i.val < t then b + i.val else h i

private lemma prefix_legal {m r : ℕ} (h : Fin r → ℕ)
    (hh : StrictMono h) (hm : ∀ i, h i < m)
    (b : ℕ) (hb : b < 2) (hp : ∀ i, h i % 2 = (b + i.val) % 2) (t : ℕ) :
    Legal m (packedPrefix b h t) := by
  have hlo := lower_bound h hh b hb hp
  refine ⟨?_, ?_, b, hb, ?_⟩
  · intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hi : i.val < t <;> by_cases hj : j.val < t
    · simp only [packedPrefix, if_pos hi, if_pos hj]
      omega
    · simp only [packedPrefix, if_pos hi, if_neg hj]
      have h := hlo j
      omega
    · omega
    · simpa only [packedPrefix, if_neg hi, if_neg hj] using hh hij
  · intro i
    by_cases hi : i.val < t
    · simp only [packedPrefix, if_pos hi]
      exact (hlo i).trans_lt (hm i)
    · simpa only [packedPrefix, if_neg hi] using hm i
  · intro i
    by_cases hi : i.val < t
    · simp only [packedPrefix, if_pos hi]
    · simpa only [packedPrefix, if_neg hi] using hp i

private lemma prefix_zero {r : ℕ} (b : ℕ) (h : Fin r → ℕ) :
    packedPrefix b h 0 = h := by
  funext i
  simp [packedPrefix]

private lemma prefix_full {r : ℕ} (b : ℕ) (h : Fin r → ℕ) :
    packedPrefix b h r = (fun i : Fin r => b + i.val) := by
  funext i
  exact if_pos i.isLt

/-- Changing only one injectively represented label gives equality or one
exchange. No combinatorial edge is assumed. -/
private lemma one_coordinate {r : ℕ} (f g : Fin r → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (i : Fin r) (he : ∀ j, j ≠ i → f j = g j) :
    labels f = labels g ∨ Exchange r (labels f) (labels g) := by
  classical
  by_cases heq : labels f = labels g
  · exact Or.inl heq
  right
  have hF : (labels f).card = r := by
    rw [labels, Finset.card_image_of_injective _ hf]
    simp
  have hG : (labels g).card = r := by
    rw [labels, Finset.card_image_of_injective _ hg]
    simp
  let C := (Finset.univ.erase i).image f
  have hC : C.card + 1 = r := by
    dsimp only [C]
    rw [Finset.card_image_of_injective _ hf]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_erase_add_one (Finset.mem_univ i)
  have hsub : C ⊆ labels f ∩ labels g := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (he j hji).symm⟩
  have hlow := Finset.card_le_card hsub
  have hlt : (labels f ∩ labels g).card < r := by
    by_contra hn
    have hI : labels f ∩ labels g = labels f :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hFG : labels f ⊆ labels g := Finset.inter_eq_left.mp hI
    exact heq (Finset.eq_of_subset_of_card_le hFG (by omega))
  exact ⟨heq, by omega⟩

private lemma prefix_step {m r : ℕ} (h : Fin r → ℕ)
    (hh : StrictMono h) (hm : ∀ i, h i < m)
    (b : ℕ) (hb : b < 2) (hp : ∀ i, h i % 2 = (b + i.val) % 2)
    (t : ℕ) (ht : t < r) :
    labels (packedPrefix b h t) = labels (packedPrefix b h (t+1)) ∨
      Exchange r (labels (packedPrefix b h t)) (labels (packedPrefix b h (t+1))) := by
  apply one_coordinate _ _
    (prefix_legal h hh hm b hb hp t).1.injective
    (prefix_legal h hh hm b hb hp (t+1)).1.injective ⟨t, ht⟩
  intro j hj
  have hne : j.val ≠ t := by
    intro he
    apply hj
    exact Fin.ext he
  have he : (j.val < t) ↔ (j.val < t+1) := by omega
  simp only [packedPrefix, he]

/-- The two packed phases differ by one boundary label, not r coordinate
moves. The r=0 case is an equality and will be removed. -/
private lemma anchor_step (r b c : ℕ) (hb : b < 2) (hc : c < 2) :
    labels (fun i : Fin r => b + i.val) = labels (fun i : Fin r => c + i.val) ∨
      Exchange r (labels (fun i : Fin r => b + i.val))
        (labels (fun i : Fin r => c + i.val)) := by
  classical
  have h01 : labels (fun i : Fin r => 0 + i.val) = labels (fun i : Fin r => 1 + i.val) ∨
      Exchange r (labels (fun i : Fin r => 0 + i.val))
        (labels (fun i : Fin r => 1 + i.val)) := by
    by_cases hr : r = 0
    · subst r
      left
      simp [labels]
    · have hr0 : 0 < r := by omega
      let f : Fin r → ℕ := fun i => i.val
      let g : Fin r → ℕ := fun i => if i.val = 0 then r else i.val
      have hf : Function.Injective f := by
        intro i j he
        exact Fin.ext he
      have hg : Function.Injective g := by
        intro i j he
        by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
        · exact Fin.ext (hi.trans hj.symm)
        · simp only [g, if_pos hi, if_neg hj] at he
          have hh := j.isLt
          omega
        · simp only [g, if_neg hi, if_pos hj] at he
          have hh := i.isLt
          omega
        · apply Fin.ext
          simpa only [g, if_neg hi, if_neg hj] using he
      have hother : ∀ j : Fin r, j ≠ ⟨0, hr0⟩ → f j = g j := by
        intro j hj
        have hn : j.val ≠ 0 := by intro he; exact hj (Fin.ext he)
        simp [f, g, hn]
      have heq : labels g = labels (fun i : Fin r => 1 + i.val) := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
          have hx0 : 0 < x ∧ x ≤ r := by
            by_cases hz : i.val = 0
            · simp only [g, if_pos hz] at hi
              omega
            · simp only [g, if_neg hz] at hi
              have hh := i.isLt
              omega
          exact Finset.mem_image.mpr ⟨⟨x-1, by omega⟩, Finset.mem_univ _, by change 1+(x-1) = x; omega⟩
        · intro hx
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
          have hh := i.isLt
          have hx0 : 0 < x ∧ x ≤ r := by
            have hi' : 1+i.val = x := hi
            omega
          by_cases hxr : x = r
          · exact Finset.mem_image.mpr ⟨⟨0, hr0⟩, Finset.mem_univ _, by simp [g, hxr]⟩
          · have hxm : x < r := by omega
            exact Finset.mem_image.mpr ⟨⟨x, hxm⟩, Finset.mem_univ _, by simp [g, ne_of_gt hx0.1]⟩
      have h := one_coordinate f g hf hg ⟨0, hr0⟩ hother
      rw [heq] at h
      simpa only [f, Nat.zero_add] using h
  have hb' : b = 0 ∨ b = 1 := by omega
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases hb' with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl rfl
  · exact h01
  · rcases h01 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (exchange_symm h)
  · exact Or.inl rfl

/-- Delete stationary transitions from an explicitly supplied finite schedule.
This helper proves compression; the schedule itself is constructed below. -/
private lemma compress_schedule {E : Type*} (valid : E → Prop) (edge : E → E → Prop)
    (N : ℕ) (a : ℕ → E)
    (hv : ∀ i, i ≤ N → valid (a i))
    (he : ∀ i, i < N → a i = a (i+1) ∨ edge (a i) (a (i+1))) :
    ∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → E,
      p 0 = a 0 ∧ p L = a N ∧ (∀ i, i ≤ L → valid (p i)) ∧
      ∀ i, i < L → edge (p i) (p (i+1)) := by
  induction N generalizing a with
  | zero =>
    refine ⟨0, le_rfl, a, rfl, rfl, hv, ?_⟩
    intro i hi
    omega
  | succ N ih =>
    obtain ⟨L, hL, p, hp0, hpL, hpv, hpe⟩ := ih (fun i => a (i+1))
      (fun i hi => hv (i+1) (by omega)) (fun i hi => he (i+1) (by omega))
    rcases he 0 (by omega) with h | h
    · refine ⟨L, by omega, p, hp0.trans h.symm, hpL, hpv, hpe⟩
    · let q : ℕ → E := fun i => match i with
        | 0 => a 0
        | j+1 => p j
      refine ⟨L+1, by omega, q, rfl, hpL, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact hv 0 (by omega)
        | succ i => exact hpv i (by omega)
      · intro i hi
        cases i with
        | zero => simpa only [q, hp0] using h
        | succ i => exact hpe i (by omega)

/-- Left-pack each phase, cross once between the anchors, and reverse the
other packing. The actual schedule uses at most 2r+1 nontrivial exchanges. -/
theorem route {m r : ℕ} (h k : Fin r → ℕ) (hh : Legal m h) (hk : Legal m k) :
    ∃ L : ℕ, L ≤ 2*r+1 ∧ ∃ p : ℕ → Finset ℕ,
      p 0 = labels h ∧ p L = labels k ∧
      (∀ i, i ≤ L → Good m r (p i)) ∧
      ∀ i, i < L → Exchange r (p i) (p (i+1)) := by
  classical
  obtain ⟨hh, hhm, b, hb, hhp⟩ := hh
  obtain ⟨hk, hkm, c, hc, hkp⟩ := hk
  let A : ℕ → Finset ℕ := fun t =>
    if t ≤ r then labels (packedPrefix b h t) else labels (packedPrefix c k (2*r+1-t))
  have hgood : ∀ t, Good m r (A t) := by
    intro t
    dsimp only [A]
    split_ifs
    · exact ⟨_, prefix_legal h hh hhm b hb hhp t, rfl⟩
    · exact ⟨_, prefix_legal k hk hkm c hc hkp (2*r+1-t), rfl⟩
  have hstep : ∀ t, t < 2*r+1 → A t = A (t+1) ∨ Exchange r (A t) (A (t+1)) := by
    intro t ht
    rcases lt_trichotomy t r with htr | htr | htr
    · have h0 : t ≤ r := by omega
      have h1 : t+1 ≤ r := by omega
      simpa only [A, if_pos h0, if_pos h1] using prefix_step h hh hhm b hb hhp t htr
    · subst t
      have h0 : ¬ (r+1 ≤ r) := by omega
      have hn : 2*r+1-(r+1) = r := by omega
      simpa only [A, if_pos (le_refl r), if_neg h0, hn, prefix_full] using anchor_step r b c hb hc
    · have h0 : ¬ (t ≤ r) := by omega
      have h1 : ¬ (t+1 ≤ r) := by omega
      let s := 2*r-t
      have hs : s < r := by dsimp only [s]; omega
      have he0 : 2*r+1-t = s+1 := by dsimp only [s]; omega
      have he1 : 2*r+1-(t+1) = s := by dsimp only [s]; omega
      have h := prefix_step k hk hkm c hc hkp s hs
      have hr : labels (packedPrefix c k (s+1)) = labels (packedPrefix c k s) ∨
          Exchange r (labels (packedPrefix c k (s+1))) (labels (packedPrefix c k s)) := by
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (exchange_symm h)
      simpa only [A, if_neg h0, if_neg h1, he0, he1] using hr
  obtain ⟨L, hL, p, hp0, hpL, hpv, hpe⟩ :=
    compress_schedule (Good m r) (Exchange r) (2*r+1) A (fun i _ => hgood i) hstep
  have hA0 : A 0 = labels h := by simp [A, prefix_zero]
  have hAN : A (2*r+1) = labels k := by
    have hn : ¬ (2*r+1 ≤ r) := by omega
    simp only [A, if_neg hn, Nat.sub_self, prefix_zero]
  exact ⟨L, hL, p, hp0.trans hA0, hpL.trans hAN, hpv, hpe⟩

/-- Complementing an exchange gives an exchange of selected original labels,
with the correct complementary cardinality. -/
private lemma complement_exchange {m r : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.range m) (hT : T ⊆ Finset.range m)
    (hcS : S.card = r) (hcT : T.card = r) (he : Exchange r S T) :
    Exchange (m-r) (Finset.range m \ S) (Finset.range m \ T) := by
  classical
  have hU : S ∪ T ⊆ Finset.range m := Finset.union_subset hS hT
  have huc := Finset.card_union_add_card_inter S T
  have hUc : (S ∪ T).card = r+1 := by have hh := he.2; omega
  have hbound := Finset.card_le_card hU
  simp only [Finset.card_range, hUc] at hbound
  have hI : (Finset.range m \ S) ∩ (Finset.range m \ T) =
      Finset.range m \ (S ∪ T) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    tauto
  refine ⟨?_, ?_⟩
  · intro hh
    apply he.1
    ext x
    by_cases hx : x ∈ Finset.range m
    · have hx' := congrArg (fun U : Finset ℕ => x ∈ U) hh
      simp only [Finset.mem_sdiff, hx, true_and] at hx'
      tauto
    · have hs : x ∉ S := fun hs => hx (hS hs)
      have ht : x ∉ T := fun ht => hx (hT ht)
      simp [hs, ht]
  · rw [hI, Finset.card_sdiff_of_subset hU, Finset.card_range, hUc]
    omega

end Hirsch.AlternatingComplement

/-- Uniform single-label exchange routes for both alternating complement
phases. All intermediate configurations are constructed; no path is a premise. -/
theorem accepted_alternating_routes (m r : ℕ) (h k : Fin r → ℕ)
    (hh : StrictMono h) (hk : StrictMono k)
    (hhm : ∀ i, h i < m) (hkm : ∀ i, k i < m)
    (hphase : ∃ b : ℕ, b < 2 ∧ ∀ i, h i % 2 = (b + i.val) % 2)
    (kphase : ∃ b : ℕ, b < 2 ∧ ∀ i, k i % 2 = (b + i.val) % 2) :
    ∃ L : ℕ, L ≤ 2*r+1 ∧ ∃ p : ℕ → Finset ℕ,
      p 0 = Finset.univ.image h ∧ p L = Finset.univ.image k ∧
      (∀ t, t ≤ L → p t ⊆ Finset.range m ∧ (p t).card = r ∧
        (Finset.range m \ p t).card = m-r ∧
        ∃ a : Fin r → ℕ, StrictMono a ∧ (∀ i, a i < m) ∧
          (∃ b : ℕ, b < 2 ∧ ∀ i, a i % 2 = (b + i.val) % 2) ∧
          Finset.univ.image a = p t) ∧
      (∀ t, t < L → p t ≠ p (t+1) ∧ (p t ∩ p (t+1)).card + 1 = r ∧
        (Finset.range m \ p t) ≠ (Finset.range m \ p (t+1)) ∧
        ((Finset.range m \ p t) ∩ (Finset.range m \ p (t+1))).card + 1 = m-r) := by
  classical
  obtain ⟨L, hL, p, hp0, hpL, hpv, hpe⟩ :=
    Hirsch.AlternatingComplement.route h k ⟨hh, hhm, hphase⟩ ⟨hk, hkm, kphase⟩
  have hv : ∀ t, t ≤ L → p t ⊆ Finset.range m ∧ (p t).card = r := by
    intro t ht
    obtain ⟨a, ha, he⟩ := hpv t ht
    rw [← he]
    exact ⟨Hirsch.AlternatingComplement.labels_subset a ha.2.1,
      Hirsch.AlternatingComplement.labels_card a ha.1⟩
  refine ⟨L, hL, p, hp0, hpL, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, ha, he⟩ := hpv t ht
    have hc : (Finset.range m \ p t).card = m-r := by
      rw [Finset.card_sdiff_of_subset (hv t ht).1, Finset.card_range, (hv t ht).2]
    exact ⟨(hv t ht).1, (hv t ht).2, hc, a, ha.1, ha.2.1, ha.2.2, he⟩
  · intro t ht
    have hs := hv t (by omega)
    have hu := hv (t+1) (by omega)
    have he := hpe t ht
    have hc := Hirsch.AlternatingComplement.complement_exchange hs.1 hu.1 hs.2 hu.2 he
    exact ⟨he.1, he.2, hc.1, hc.2⟩


/-! New finite-set bridge: actual Gale-even sets, not supplied enumerations. -/
namespace Hirsch.GaleGapRoutes

/-- The literal selected-label predicate used by the moment parity catalogue. -/
def EvenGaps {m : ℕ} (S : Finset (Fin m)) : Prop :=
  ∀ i ∉ S, ∀ j ∉ S, i < j →
    (S.filter (fun s => i < s ∧ s < j)).card % 2 = 0

/-- The number of selected labels below a hole, plus its rank, equals its label. -/
lemma rank_balance {m r : ℕ} (S : Finset (Fin m)) (h : Fin r → Fin m)
    (hh : StrictMono h) (himage : Finset.univ.image h = Finset.univ \ S)
    (i : Fin r) :
    (S.filter (fun s => s < h i)).card + i.val = (h i).val := by
  classical
  have hholes : ((Finset.univ \ S).filter (fun s => s < h i)).card = i.val := by
    have he : (Finset.univ \ S).filter (fun s => s < h i) =
        (Finset.Iio i).image h := by
      rw [← himage]
      ext x
      constructor
      · intro hx
        obtain ⟨hx,hlt⟩ := Finset.mem_filter.mp hx
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨j,Finset.mem_Iio.mpr (hh.lt_iff_lt.mp hlt),rfl⟩
      · intro hx
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,hh (Finset.mem_Iio.mp hj)⟩
    rw [he,Finset.card_image_of_injective _ hh.injective,Fin.card_Iio]
  have hd : Disjoint (S.filter (fun s => s < h i))
      ((Finset.univ \ S).filter (fun s => s < h i)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2
      (Finset.mem_filter.mp hx).1
  have he : (S.filter (fun s => s < h i)) ∪
      ((Finset.univ \ S).filter (fun s => s < h i)) = Finset.Iio (h i) := by
    ext x
    simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_sdiff,
      Finset.mem_univ,true_and,Finset.mem_Iio]
    tauto
  calc
    (S.filter (fun s => s < h i)).card + i.val =
        (S.filter (fun s => s < h i)).card +
          ((Finset.univ \ S).filter (fun s => s < h i)).card := by rw [hholes]
    _ = ((S.filter (fun s => s < h i)) ∪
          ((Finset.univ \ S).filter (fun s => s < h i))).card :=
      (Finset.card_union_of_disjoint hd).symm
    _ = (h i).val := by rw [he,Fin.card_Iio]

lemma below_gap {m : ℕ} (S : Finset (Fin m)) (i j : Fin m)
    (hi : i ∉ S) (hij : i < j) :
    (S.filter (fun s => s < j)).card =
      (S.filter (fun s => s < i)).card +
        (S.filter (fun s => i < s ∧ s < j)).card := by
  classical
  have he : S.filter (fun s => s < j) =
      S.filter (fun s => s < i) ∪ S.filter (fun s => i < s ∧ s < j) := by
    ext s
    simp only [Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨hs,hsj⟩
      rcases lt_trichotomy s i with hsi | hsi | his
      · exact Or.inl ⟨hs,hsi⟩
      · subst s
        exact False.elim (hi hs)
      · exact Or.inr ⟨hs,his,hsj⟩
    · rintro (⟨hs,hsi⟩ | ⟨hs,his,hsj⟩)
      · exact ⟨hs,hsi.trans hij⟩
      · exact ⟨hs,hsj⟩
  have hd : Disjoint (S.filter (fun s => s < i))
      (S.filter (fun s => i < s ∧ s < j)) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    exact (lt_asymm (Finset.mem_filter.mp hs).2) (Finset.mem_filter.mp ht).2.1
  rw [he,Finset.card_union_of_disjoint hd]

/-- Even selected gaps are equivalent to alternating indexed hole parity.
The empty complement is covered, with a vacuous phase witness. -/
theorem even_gaps_iff_phase {m r : ℕ} (S : Finset (Fin m)) (h : Fin r → Fin m)
    (hh : StrictMono h) (himage : Finset.univ.image h = Finset.univ \ S) :
    EvenGaps S ↔ ∃ b : ℕ, b < 2 ∧ ∀ i, (h i).val % 2 = (b+i.val) % 2 := by
  classical
  have hnot : ∀ i, h i ∉ S := by
    intro i
    have hi : h i ∈ Finset.univ.image h := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rw [himage] at hi
    exact (Finset.mem_sdiff.mp hi).2
  constructor
  · intro hg
    by_cases hr : r = 0
    · subst r
      exact ⟨0,by omega,fun i => Fin.elim0 i⟩
    have hr0 : 0 < r := by omega
    let z : Fin r := ⟨0,hr0⟩
    refine ⟨(h z).val % 2,Nat.mod_lt _ (by omega),?_⟩
    intro i
    by_cases hi : i = z
    · subst i
      simp only [z,Fin.val_mk,Nat.add_zero,Nat.mod_mod]
    have hzi : z < i := by
      change 0 < i.val
      have hne : i.val ≠ 0 := by
        intro he
        apply hi
        exact Fin.ext he
      omega
    have hg' := hg (h z) (hnot z) (h i) (hnot i) (hh hzi)
    have h0 := rank_balance S h hh himage z
    have h1 := rank_balance S h hh himage i
    have hsum := below_gap S (h z) (h i) (hnot z) (hh hzi)
    change (S.filter (fun s => s < h z)).card + 0 = (h z).val at h0
    omega
  · rintro ⟨b,hb,hphase⟩ i hi j hj hij
    have hiH : i ∈ Finset.univ.image h := by
      rw [himage]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩
    have hjH : j ∈ Finset.univ.image h := by
      rw [himage]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩
    obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hiH
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hjH
    subst i
    subst j
    have h0 := rank_balance S h hh himage u
    have h1 := rank_balance S h hh himage v
    have hsum := below_gap S (h u) (h v) hi hij
    have hp0 := hphase u
    have hp1 := hphase v
    omega

/-- Original finite labels and their natural-number values are transported
injectively; no out-of-range labels are silently reduced modulo m. -/
def natLabels {m : ℕ} (S : Finset (Fin m)) : Finset ℕ := S.image Fin.val

def decode (m : ℕ) (S : Finset ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i.val ∈ S)

lemma mem_decode {m : ℕ} (S : Finset ℕ) (i : Fin m) :
    i ∈ decode m S ↔ i.val ∈ S := by simp [decode]

lemma mem_natLabels {m : ℕ} (S : Finset (Fin m)) (i : Fin m) :
    i.val ∈ natLabels S ↔ i ∈ S := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    have hji : j = i := Fin.ext he
    exact hji ▸ hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩

lemma natLabels_card {m : ℕ} (S : Finset (Fin m)) :
    (natLabels S).card = S.card :=
  Finset.card_image_of_injective S Fin.val_injective

lemma natLabels_decode {m : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.range m) :
    natLabels (decode m S) = S := by
  ext n
  constructor
  · intro hn
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hn
    exact he ▸ (mem_decode S i).mp hi
  · intro hn
    have hnm : n < m := Finset.mem_range.mp (hS hn)
    exact Finset.mem_image.mpr
      ⟨⟨n,hnm⟩,(mem_decode S ⟨n,hnm⟩).mpr hn,rfl⟩

lemma decode_card {m : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.range m) :
    (decode m S).card = S.card := by
  rw [← natLabels_card, natLabels_decode S hS]

lemma natLabels_inter {m : ℕ} (S T : Finset (Fin m)) :
    natLabels (S ∩ T) = natLabels S ∩ natLabels T := by
  ext n
  constructor
  · intro hn
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_inter.mpr
      ⟨(mem_natLabels S i).mpr (Finset.mem_inter.mp hi).1,
       (mem_natLabels T i).mpr (Finset.mem_inter.mp hi).2⟩
  · intro hn
    obtain ⟨hs,ht⟩ := Finset.mem_inter.mp hn
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr
      ⟨i,Finset.mem_inter.mpr ⟨hi,(mem_natLabels T i).mp ht⟩,rfl⟩

lemma decode_complement {m : ℕ} (S : Finset (Fin m)) :
    decode m (Finset.range m \ natLabels (Finset.univ \ S)) = S := by
  ext i
  rw [mem_decode,Finset.mem_sdiff,Finset.mem_range,mem_natLabels]
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,i.isLt,true_and,not_not]

/-- Derive the ordered, bounded, phased complement from a finite selected set.
Its exact cardinality and image are conclusions, not input enumerations. -/
theorem enumerate_complement {m d : ℕ} (S : Finset (Fin m))
    (hS : S.card = d) (hg : EvenGaps S) :
    ∃ h : Fin (m-d) → ℕ, StrictMono h ∧ (∀ i, h i < m) ∧
      (∃ b : ℕ, b < 2 ∧ ∀ i, h i % 2 = (b+i.val) % 2) ∧
      Finset.univ.image h = natLabels (Finset.univ \ S) := by
  classical
  let H : Finset (Fin m) := Finset.univ \ S
  have hH : H.card = m-d := by
    dsimp [H]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ,Fintype.card_fin,hS]
  let e : Fin (m-d) ↪o Fin m := H.orderEmbOfFin hH
  have he : Finset.univ.image e = Finset.univ \ S := by
    exact Finset.image_orderEmbOfFin_univ H hH
  have hphase := (even_gaps_iff_phase S e e.strictMono he).mp hg
  refine ⟨fun i => (e i).val,?_,fun i => (e i).isLt,hphase,?_⟩
  · intro i j hij
    exact e.strictMono hij
  · change Finset.univ.image (fun i => (e i).val) = (Finset.univ \ S).image Fin.val
    rw [← he,Finset.image_image]
    rfl

/-- A legal alternating natural-label configuration gives the exact even-gap
predicate on its selected finite complement. This also covers empty holes. -/
lemma decode_legal_complement {m r : ℕ} (h : Fin r → ℕ)
    (hh : StrictMono h) (hm : ∀ i, h i < m)
    (hphase : ∃ b : ℕ, b < 2 ∧ ∀ i, h i % 2 = (b+i.val) % 2) :
    EvenGaps (decode m (Finset.range m \ Finset.univ.image h)) := by
  classical
  let f : Fin r → Fin m := fun i => ⟨h i,hm i⟩
  have hf : StrictMono f := by
    intro i j hij
    exact hh hij
  have he : Finset.univ.image f =
      Finset.univ \ decode m (Finset.range m \ Finset.univ.image h) := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,mem_decode,
      Finset.mem_range,i.isLt,true_and,not_not]
    constructor
    · intro hi
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hi
      have hv : h j = i.val := congrArg Fin.val hj
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hv⟩
    · intro hi
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,Fin.ext hj⟩
  exact (even_gaps_iff_phase _ f hf he).mpr hphase

/-- Construct bounded exchanges directly from selected-set Gale evenness. -/
theorem selected_routes (m d : ℕ) (S T : Finset (Fin m))
    (hS : S.card = d) (hT : T.card = d) (hgS : EvenGaps S) (hgT : EvenGaps T) :
    ∃ L : ℕ, L ≤ 2*(m-d)+1 ∧ ∃ p : ℕ → Finset (Fin m),
      p 0 = S ∧ p L = T ∧
      (∀ t, t ≤ L → (p t).card = d ∧ EvenGaps (p t)) ∧
      ∀ t, t < L → p t ≠ p (t+1) ∧ (p t ∩ p (t+1)).card + 1 = d := by
  classical
  have hd : d ≤ m := by
    have hc := Finset.card_le_card (Finset.subset_univ S)
    simpa only [Finset.card_univ,Fintype.card_fin,hS] using hc
  have hdd : m-(m-d) = d := by omega
  obtain ⟨h,hh,hhm,hphase,heh⟩ := enumerate_complement S hS hgS
  obtain ⟨k,hk,hkm,kphase,hek⟩ := enumerate_complement T hT hgT
  obtain ⟨L,hL,q,hq0,hqL,hqv,hqe⟩ :=
    accepted_alternating_routes m (m-d) h k hh hk hhm hkm hphase kphase
  let p : ℕ → Finset (Fin m) := fun t => decode m (Finset.range m \ q t)
  have hnatural : ∀ t, natLabels (p t) = Finset.range m \ q t := by
    intro t
    exact natLabels_decode _ (Finset.sdiff_subset)
  refine ⟨L,hL,p,?_,?_,?_,?_⟩
  · dsimp only [p]
    rw [hq0,heh,decode_complement]
  · dsimp only [p]
    rw [hqL,hek,decode_complement]
  · intro t ht
    obtain ⟨hsub,hcard,hcc,a,ha,ham,hap,haq⟩ := hqv t ht
    constructor
    · calc
        (p t).card = (Finset.range m \ q t).card := decode_card _ Finset.sdiff_subset
        _ = d := hcc.trans hdd
    · change EvenGaps (decode m (Finset.range m \ q t))
      rw [← haq]
      exact decode_legal_complement a ha ham hap
  · intro t ht
    have he := hqe t ht
    constructor
    · intro hp
      have hn := congrArg natLabels hp
      rw [hnatural t,hnatural (t+1)] at hn
      exact he.2.2.1 hn
    · have hc : (p t ∩ p (t+1)).card =
          ((Finset.range m \ q t) ∩ (Finset.range m \ q (t+1))).card := by
        rw [← natLabels_card,natLabels_inter,hnatural t,hnatural (t+1)]
      rw [hc]
      exact he.2.2.2.trans hdd

end Hirsch.GaleGapRoutes

set_option maxHeartbeats 5000000

namespace Hirsch.MomentLinearRoutes

open Set MomentBarycentric MomentVertices MomentRootCatalogue MomentEvenGaps

lemma mem_parity_catalogue {d m : ℕ} (S : Finset (Fin m)) :
    S ∈ parityCatalogue d m ↔ S.card = d ∧ MomentEvenGaps.EvenGaps S := by
  classical
  simp [parityCatalogue, Finset.mem_powersetCard]

/-- Assemble the complete geometric route, not merely a legal label walk.
Both endpoints are arbitrary actual extreme points of the original H system. -/
theorem all_endpoint_original_routes {d m : ℕ} (a : Fin m → ℝ)
    (ha : StrictMono a) (hm : d < m) (u v : Fin d → ℝ)
    (hu : u ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ)
    (hv : v ∈ ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ) :
    ∃ L : ℕ, L ≤ 2 * (m-d) + 1 ∧ ∃ p : ℕ → (Fin d → ℝ),
      p 0 = u ∧ p L = v ∧
      (∀ t, t ≤ L → p t ∈
        ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ) ∧
      ∀ t, t < L → p t ≠ p (t+1) ∧
        IsExposed ℝ {x : Fin d → ℝ | ∀ i, row a x i ≤ 1}
          (segment ℝ (p t) (p (t+1))) ∧
        IsExtreme ℝ {x : Fin d → ℝ | ∀ i, row a x i ≤ 1}
          (segment ℝ (p t) (p (t+1))) ∧
        {z : Fin d → ℝ | (∀ i, row a z i ≤ 1) ∧
          ∀ i ∈ active a (p t) ∩ active a (p (t+1)), row a z i = 1} =
            segment ℝ (p t) (p (t+1)) := by
  classical
  obtain ⟨hnorm, hinj, hvertices, htight, hcount, hbound⟩ :=
    complete_even_catalogue a ha hm
  obtain ⟨S, hS, heS⟩ := Finset.mem_image.mp ((hvertices u).mp hu)
  obtain ⟨T, hT, heT⟩ := Finset.mem_image.mp ((hvertices v).mp hv)
  have hSc := (mem_parity_catalogue S).mp hS
  have hTc := (mem_parity_catalogue T).mp hT
  obtain ⟨L, hL, q, hq0, hqL, hqv, hqe⟩ :=
    GaleGapRoutes.selected_routes m d S T hSc.1 hTc.1 hSc.2 hTc.2
  let p : ℕ → (Fin d → ℝ) := fun t => candidate (d:=d) a (q t)
  have hmem : ∀ t, t ≤ L → q t ∈ parityCatalogue d m := by
    intro t ht
    exact (mem_parity_catalogue (q t)).mpr (hqv t ht)
  have hvertex : ∀ t, t ≤ L → p t ∈
      ({x : Fin d → ℝ | ∀ i, row a x i ≤ 1}).extremePoints ℝ := by
    intro t ht
    apply (hvertices (p t)).mpr
    exact Finset.mem_image.mpr ⟨q t, hmem t ht, rfl⟩
  have hact : ∀ t, t ≤ L → active a (p t) = q t := by
    intro t ht
    ext i
    rw [mem_active]
    exact htight (q t) (hmem t ht) i
  refine ⟨L, hL, p, ?_, ?_, hvertex, ?_⟩
  · change candidate (d:=d) a (q 0) = u
    rw [hq0]
    exact heS
  · change candidate (d:=d) a (q L) = v
    rw [hqL]
    exact heT
  · intro t ht
    have ht0 : t ≤ L := by omega
    have ht1 : t+1 ≤ L := by omega
    have h0 := hvertex t ht0
    have h1 := hvertex (t+1) ht1
    have hne : p t ≠ p (t+1) := by
      intro he
      apply (hqe t ht).1
      calc
        q t = active a (p t) := (hact t ht0).symm
        _ = active a (p (t+1)) := congrArg (active a) he
        _ = q (t+1) := hact (t+1) ht1
    have hc0 : (active a (p t)).card = d := by
      rw [hact t ht0]
      exact (hqv t ht0).1
    have hc1 : (active a (p (t+1))).card = d := by
      rw [hact (t+1) ht1]
      exact (hqv (t+1) ht1).1
    have hc : (active a (p t) ∩ active a (p (t+1))).card+1 = d := by
      rw [hact t ht0, hact (t+1) ht1]
      exact (hqe t ht).2
    have hex := MomentEdges.exposed_edge a ha.injective hm (p t) (p (t+1))
      h0.1 h1.1 hc0 hc1 hc
    have hslice := MomentEdges.common_slice_eq_segment a ha.injective hm (p t) (p (t+1))
      h0.1 h1.1 hc0 hc1 hc
    exact ⟨hne, hex, hex.isExtreme, hslice⟩

end Hirsch.MomentLinearRoutes

/-- A coefficient-independent linear original-edge bound for all endpoint
vertices of the ordered mean-centered moment family. -/
theorem solution (d m : ℕ) (hm : d < m) (a : Fin m → ℝ) (ha : StrictMono a)
    (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    u ∈ P.extremePoints ℝ → v ∈ P.extremePoints ℝ →
      ∃ L : ℕ, L ≤ 2 * (m-d) + 1 ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0 = u ∧ p L = v ∧ (∀ t, t ≤ L → p t ∈ P.extremePoints ℝ) ∧
        ∀ t, t < L → p t ≠ p (t+1) ∧
          IsExposed ℝ P (segment ℝ (p t) (p (t+1))) ∧
          IsExtreme ℝ P (segment ℝ (p t) (p (t+1))) ∧
          {z | z ∈ P ∧ ∀ i, row (p t) i = 1 → row (p (t+1)) i = 1 → row z i = 1} =
            segment ℝ (p t) (p (t+1)) := by
  classical
  dsimp only
  intro hu hv
  obtain ⟨L, hL, p, hp0, hpL, hpv, hpe⟩ :=
    Hirsch.MomentLinearRoutes.all_endpoint_original_routes a ha hm u v hu hv
  refine ⟨L, hL, p, hp0, hpL, hpv, ?_⟩
  intro t ht
  obtain ⟨hne, hex, hext, hs⟩ := hpe t ht
  refine ⟨hne, hex, hext, ?_⟩
  simpa only [Finset.mem_inter, Hirsch.MomentVertices.mem_active, and_imp] using hs

#print axioms Hirsch.MomentEvenGaps.complete_even_catalogue
#print axioms Hirsch.GaleGapRoutes.selected_routes
#print axioms Hirsch.MomentEdges.exposed_edge
#print axioms Hirsch.MomentLinearRoutes.all_endpoint_original_routes
#print axioms solution
