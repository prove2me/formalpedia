-- Prove2me | solution 2 for BookSixth.drawing_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T09:26:31.930347+00:00
-- url     : https://prove2.me/submissions/5ad75561-f7de-4cde-a371-8404ab1edf5b

import Mathlib
import Definitions.Def_BookSixth

/-! Crossing-lemma build library (BookSixth: b2255bec -> 6968bb2a -> 634d53d7).
Route: continuous crossing-free drawing -> polygonal (PL) drawing (spokes + loop erasure)
-> sheared so all points have distinct X -> vertical-sweep "gap graph" H ->
#components(H) >= 1 + E - n (Laplacian kernel) and <= 2E/3 (face-walk map phi, fibres >= 3)
-> E <= 3n. No Jordan curve theorem is used. See PLAN.md / NOTES.md in this folder.
Only finished, compiled lemmas live here; unfinished statements stay in NOTES.md. -/

open BookSixth

namespace CrB

/-! ## M1: sampling reduction, conditional on the edge bound -/

/-- A crossing-free set of edges: distinct edges have disjoint interiors. -/
def FreeSet {N M : ℕ} (D : PlaneDrawing N M) (E : Finset (Fin M)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ t s : EdgeParameter,
    0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 → D.arc e t ≠ D.arc f s

/-- The edge bound (the statement of b2255bec) for one drawing. -/
def EdgeBoundFor {N M : ℕ} (D : PlaneDrawing N M) : Prop :=
  ∀ (V : Finset (Fin N)) (E : Finset (Fin M)), (∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V) →
    FreeSet D E → E.card ≤ 3 * V.card

/-- Product weight of a vertex sample. -/
noncomputable def wt {N : ℕ} (p : ℝ) (x : Fin N → Bool) : ℝ :=
  ∏ v, (if x v = true then p else 1 - p)

theorem wt_nonneg {N : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin N → Bool) :
    0 ≤ wt p x := by
  unfold wt
  apply Finset.prod_nonneg
  intro v _
  split_ifs
  · exact hp
  · linarith

theorem sampling_identity {N : ℕ} (T : Finset (Fin N)) (p : ℝ) :
    (∑ x : Fin N → Bool, if ∀ v ∈ T, x v = true then wt p x else 0) = p ^ T.card := by
  classical
  have h1 : ∀ x : Fin N → Bool, (if ∀ v ∈ T, x v = true then wt p x else 0)
      = ∏ v, (if v ∈ T then (if x v = true then p else 0)
          else (if x v = true then p else 1 - p)) := by
    intro x
    split_ifs with h
    · apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ T
      · simp only [hv, h v hv, if_true]
      · simp only [hv, if_false]
    · simp only [not_forall] at h
      obtain ⟨v, hv, hxv⟩ := h
      rw [Bool.not_eq_true] at hxv
      refine (Finset.prod_eq_zero (Finset.mem_univ v) ?_).symm
      simp only [hv, if_true, hxv, Bool.false_eq_true, if_false]
  have h3 := Fintype.prod_sum (κ := fun _ : Fin N => Bool)
    (fun v b => if v ∈ T then (if b = true then p else 0) else (if b = true then p else 1 - p))
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← h3]
  have h2 : ∀ v, (∑ b : Bool, (if v ∈ T then (if b = true then p else 0)
      else (if b = true then p else 1 - p))) = if v ∈ T then p else 1 := by
    intro v
    by_cases hv : v ∈ T <;> simp [hv]
  rw [Finset.prod_congr rfl (fun v _ => h2 v), Fintype.prod_ite_mem, Finset.prod_const]

theorem avg_indicator {N : ℕ} (T : Finset (Fin N)) (P : (Fin N → Bool) → Prop)
    [DecidablePred P] (hP : ∀ x, P x ↔ ∀ v ∈ T, x v = true) (p : ℝ) :
    ∑ x, wt p x * (if P x then (1 : ℝ) else 0) = p ^ T.card := by
  classical
  rw [← sampling_identity T p]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_ite, mul_one, mul_zero]
  by_cases h : P x
  · rw [if_pos h, if_pos ((hP x).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((hP x).mpr h'))]

theorem hgeom_of_edgeBound {N M : ℕ} (D : PlaneDrawing N M) (EB : EdgeBoundFor D)
    (x : Fin N → Bool) :
    (∑ e : Fin M, if x (D.left e) = true ∧ x (D.right e) = true then (1 : ℝ) else 0) ≤
      3 * (∑ v, if x v = true then (1 : ℝ) else 0) +
      ∑ c ∈ D.crossings, if x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
        x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true then (1 : ℝ) else 0 := by
  classical
  set S : Finset (Fin N) := Finset.univ.filter (fun v => x v = true) with hS
  set ES : Finset (Fin M) := Finset.univ.filter
    (fun e => x (D.left e) = true ∧ x (D.right e) = true) with hES
  set CS := D.crossings.filter (fun c => x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
        x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true) with hCS
  set R : Finset (Fin M) := CS.image (fun c => c.1.1) with hR
  have hmemES : ∀ e, e ∈ ES ↔ x (D.left e) = true ∧ x (D.right e) = true := by
    intro e; simp only [hES, Finset.mem_filter, Finset.mem_univ, true_and]
  have hend : ∀ e ∈ ES \ R, D.left e ∈ S ∧ D.right e ∈ S := by
    intro e he
    have h := (hmemES e).mp (Finset.mem_sdiff.mp he).1
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hfree : FreeSet D (ES \ R) := by
    intro e he f hf hef t s ht0 ht1 hs0 hs1 heq
    have he' := Finset.mem_sdiff.mp he
    have hf' := Finset.mem_sdiff.mp hf
    have hxe := (hmemES e).mp he'.1
    have hxf := (hmemES f).mp hf'.1
    rcases lt_or_gt_of_ne hef with hlt | hlt
    · have hc : ((e, f), D.arc e t) ∈ D.crossings :=
        (D.crossings_exact e f _).mpr ⟨hlt, t, s, ht0, ht1, hs0, hs1, rfl, heq.symm⟩
      have hcs : ((e, f), D.arc e t) ∈ CS := by
        simp only [hCS, Finset.mem_filter]
        exact ⟨hc, hxe.1, hxe.2, hxf.1, hxf.2⟩
      exact he'.2 (Finset.mem_image.mpr ⟨_, hcs, rfl⟩)
    · have hc : ((f, e), D.arc f s) ∈ D.crossings :=
        (D.crossings_exact f e _).mpr ⟨hlt, s, t, hs0, hs1, ht0, ht1, rfl, heq⟩
      have hcs : ((f, e), D.arc f s) ∈ CS := by
        simp only [hCS, Finset.mem_filter]
        exact ⟨hc, hxf.1, hxf.2, hxe.1, hxe.2⟩
      exact hf'.2 (Finset.mem_image.mpr ⟨_, hcs, rfl⟩)
  have hb := EB S (ES \ R) hend hfree
  have hnat : ES.card ≤ 3 * S.card + CS.card := by
    have h1 := Finset.card_le_card_sdiff_add_card (s := ES) (t := R)
    have h2 : R.card ≤ CS.card := Finset.card_image_le
    omega
  have hreal : (ES.card : ℝ) ≤ 3 * (S.card : ℝ) + (CS.card : ℝ) := by exact_mod_cast hnat
  simp only [Finset.sum_boole]
  exact hreal

theorem sampling_of_edgeBound {N M : ℕ} (D : PlaneDrawing N M) (EB : EdgeBoundFor D) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ 2 * (M : ℝ) ≤ 3 * p * (N : ℝ) + p ^ 4 * (D.crossings.card : ℝ) := by
  classical
  -- per-sample inequality, weighted and summed
  have key : ∑ x : Fin N → Bool, wt p x *
      (∑ e : Fin M, if x (D.left e) = true ∧ x (D.right e) = true then (1 : ℝ) else 0) ≤
      ∑ x : Fin N → Bool, wt p x * (3 * (∑ v, if x v = true then (1 : ℝ) else 0) +
      ∑ c ∈ D.crossings, if x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
        x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hgeom_of_edgeBound D EB x) (wt_nonneg hp hp1 x)
  have hL : ∑ x : Fin N → Bool, wt p x *
      (∑ e : Fin M, if x (D.left e) = true ∧ x (D.right e) = true then (1 : ℝ) else 0)
      = (M : ℝ) * p ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ e : Fin M, ∑ x : Fin N → Bool,
        wt p x * (if x (D.left e) = true ∧ x (D.right e) = true then (1 : ℝ) else 0) = p ^ 2 := by
      intro e
      have hc : ({D.left e, D.right e} : Finset (Fin N)).card = 2 :=
        Finset.card_pair (D.no_loop e)
      rw [← hc]
      apply avg_indicator
      intro y
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    rw [Finset.sum_congr rfl (fun e _ => this e), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hV : ∀ v : Fin N, ∑ x : Fin N → Bool,
      wt p x * (if x v = true then (1 : ℝ) else 0) = p := by
    intro v
    have h := avg_indicator {v} (fun y : Fin N → Bool => y v = true)
      (by intro y; simp only [Finset.mem_singleton, forall_eq]) p
    rw [Finset.card_singleton, pow_one] at h
    exact h
  have hC : ∀ c ∈ D.crossings, ∑ x : Fin N → Bool,
      wt p x * (if x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
        x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true then (1 : ℝ) else 0) = p ^ 4 := by
    intro c hc
    obtain ⟨⟨e, f⟩, z⟩ := c
    have hi := D.independent_crossings e f z hc
    have he := D.no_loop e
    have hf := D.no_loop f
    have hcard : ({D.left e, D.right e, D.left f, D.right f} : Finset (Fin N)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hf]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hi.2.2.1, hi.2.2.2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨he, hi.1, hi.2.1⟩
    rw [← hcard]
    apply avg_indicator
    intro y
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  have hR : ∑ x : Fin N → Bool, wt p x * (3 * (∑ v, if x v = true then (1 : ℝ) else 0) +
      ∑ c ∈ D.crossings, if x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
        x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true then (1 : ℝ) else 0)
      = 3 * ((N : ℝ) * p) + (D.crossings.card : ℝ) * p ^ 4 := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := D.crossings)]
    have e1 : ∀ v : Fin N, ∑ x : Fin N → Bool,
        wt p x * (3 * (if x v = true then (1 : ℝ) else 0)) = 3 * p := by
      intro v
      calc ∑ x : Fin N → Bool, wt p x * (3 * (if x v = true then (1 : ℝ) else 0))
          = 3 * ∑ x : Fin N → Bool, wt p x * (if x v = true then (1 : ℝ) else 0) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
        _ = 3 * p := by rw [hV v]
    rw [Finset.sum_congr rfl (fun v _ => e1 v), Finset.sum_congr rfl hC, Finset.sum_const,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [hL, hR] at key
  linarith


/-! ## M2: affine heights, straight-line drawings, strips -/

abbrev Pt := ℝ × ℝ
abbrev Sg := Pt × Pt

noncomputable def slope (s : Sg) : ℝ := (s.2.2 - s.1.2) / (s.2.1 - s.1.1)
noncomputable def hgt (s : Sg) (x : ℝ) : ℝ := s.1.2 + (x - s.1.1) * slope s

theorem hgt_sub (s : Sg) (x y : ℝ) : hgt s x - hgt s y = (x - y) * slope s := by
  unfold hgt; ring

theorem hgt_fst (s : Sg) : hgt s s.1.1 = s.1.2 := by unfold hgt; ring

theorem hgt_snd (s : Sg) (h : s.1.1 < s.2.1) : hgt s s.2.1 = s.2.2 := by
  have hne : s.2.1 - s.1.1 ≠ 0 := (sub_pos.mpr h).ne'
  unfold hgt slope
  field_simp
  ring

/-- `q` lies on the (x-oriented) closed segment `s`. -/
def onSeg (s : Sg) (q : Pt) : Prop := s.1.1 ≤ q.1 ∧ q.1 ≤ s.2.1 ∧ q.2 = hgt s q.1

theorem affine_zero {u v c d : ℝ} (huv : u < v) (hc : c < 0) (hv : 0 < c + (v - u) * d) :
    ∃ x, u < x ∧ x < v ∧ c + (x - u) * d = 0 := by
  have hd : 0 < d := by
    by_contra h
    rw [not_lt] at h
    have : (v - u) * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    linarith
  have h1 : 0 < -c / d := div_pos (by linarith) hd
  have h2 : -c / d < v - u := by rw [div_lt_iff₀ hd]; linarith
  refine ⟨u + -c / d, by linarith, by linarith, ?_⟩
  field_simp
  ring

theorem exists_sep (A B : Finset ℝ) (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ m : ℝ, (∀ a ∈ A, a < m) ∧ ∀ b ∈ B, m < b := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · rcases B.eq_empty_or_nonempty with hB | hB
    · exact ⟨0, by simp [hA], by simp [hB]⟩
    · refine ⟨B.min' hB - 1, by simp [hA], fun b hb => ?_⟩
      have := B.min'_le b hb
      linarith
  · rcases B.eq_empty_or_nonempty with hB | hB
    · refine ⟨A.max' hA + 1, fun a ha => ?_, by simp [hB]⟩
      have := A.le_max' a ha
      linarith
    · have hlt : A.max' hA < B.min' hB := h _ (A.max'_mem hA) _ (B.min'_mem hB)
      refine ⟨(A.max' hA + B.min' hB) / 2, fun a ha => ?_, fun b hb => ?_⟩
      · have := A.le_max' a ha
        linarith
      · have := B.min'_le b hb
        linarith

/-- A straight-line plane drawing: points `P` with distinct abscissae, segments `S` oriented
left to right, meeting each other only at points of `P`, and containing points of `P` only at
their endpoints. -/
structure SL where
  P : Finset Pt
  S : Finset Sg
  hor : ∀ s ∈ S, s.1.1 < s.2.1
  mem1 : ∀ s ∈ S, s.1 ∈ P
  mem2 : ∀ s ∈ S, s.2 ∈ P
  xinj : ∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q
  disj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∀ q, onSeg s q → onSeg t q → q ∈ P
  avoid : ∀ s ∈ S, ∀ q ∈ P, onSeg s q → q = s.1 ∨ q = s.2

namespace SL
variable (G : SL)

/-- Height order between two segments cannot change over an interval free of point abscissae. -/
theorem persist {s t : Sg} (hs : s ∈ G.S) (ht : t ∈ G.S) (hst : s ≠ t)
    {u v : ℝ} (huv : u < v) (hsu : s.1.1 ≤ u) (hsv : v ≤ s.2.1) (htu : t.1.1 ≤ u)
    (htv : v ≤ t.2.1) (hgap : ∀ p ∈ G.P, ¬ (u < p.1 ∧ p.1 < v))
    (h : hgt s u < hgt t u) : hgt s v ≤ hgt t v := by
  by_contra hlt
  rw [not_le] at hlt
  have e3 := hgt_sub s v u
  have e4 := hgt_sub t v u
  obtain ⟨x, hx1, hx2, hx⟩ := affine_zero (c := hgt s u - hgt t u) (d := slope s - slope t)
    huv (by linarith) (by linarith)
  have e1 := hgt_sub s x u
  have e2 := hgt_sub t x u
  have heq : hgt s x = hgt t x := by linear_combination e1 - e2 + hx
  have hq := G.disj s hs t ht hst (x, hgt s x) ⟨by simp only; linarith, by simp only; linarith, rfl⟩
    ⟨by simp only; linarith, by simp only; linarith, heq⟩
  exact hgap _ hq ⟨hx1, hx2⟩

noncomputable def rk (p : Pt) : ℕ := (G.P.filter (fun q => q.1 < p.1)).card

theorem rk_lt_card {p : Pt} (hp : p ∈ G.P) : G.rk p < G.P.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨p, hp, lt_irrefl _⟩)

theorem rk_le_of_le {p q : Pt} (h : p.1 ≤ q.1) : G.rk p ≤ G.rk q :=
  Finset.card_le_card (fun x hx => by
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩)

theorem rk_lt_of_lt {p q : Pt} (hp : p ∈ G.P) (h : p.1 < q.1) : G.rk p < G.rk q := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨p, Finset.mem_filter.mpr ⟨hp, h⟩, fun h' => lt_irrefl _ (Finset.mem_filter.mp h').2⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem rk_inj {p q : Pt} (hp : p ∈ G.P) (hq : q ∈ G.P) (h : G.rk p = G.rk q) : p = q := by
  rcases lt_trichotomy p.1 q.1 with h1 | h1 | h1
  · have := G.rk_lt_of_lt hp h1
    omega
  · exact G.xinj p hp q hq h1
  · have := G.rk_lt_of_lt hq h1
    omega

theorem exists_sample (i : ℕ) : ∃ m : ℝ, ∀ p ∈ G.P, (p.1 < m ↔ G.rk p < i) ∧ p.1 ≠ m := by
  obtain ⟨m, hA, hB⟩ := exists_sep ((G.P.filter (fun p => G.rk p < i)).image Prod.fst)
    ((G.P.filter (fun p => ¬ G.rk p < i)).image Prod.fst) (by
      intro a ha b hb
      simp only [Finset.mem_image, Finset.mem_filter] at ha hb
      obtain ⟨p, ⟨hp, hpi⟩, rfl⟩ := ha
      obtain ⟨q, ⟨hq, hqi⟩, rfl⟩ := hb
      by_contra hle
      rw [not_lt] at hle
      have := G.rk_le_of_le hle
      omega)
  refine ⟨m, fun p hp => ?_⟩
  by_cases hpi : G.rk p < i
  · have := hA p.1 (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpi⟩, rfl⟩)
    exact ⟨⟨fun _ => hpi, fun _ => this⟩, this.ne⟩
  · have := hB p.1 (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpi⟩, rfl⟩)
    exact ⟨⟨fun h => absurd h (not_lt.mpr this.le), fun h => absurd h hpi⟩, this.ne'⟩

/-- Sample abscissa of strip `i`: exactly the points of rank `< i` lie to its left. -/
noncomputable def m (i : ℕ) : ℝ := Classical.choose (G.exists_sample i)

theorem m_spec (i : ℕ) {p : Pt} (hp : p ∈ G.P) : (p.1 < G.m i ↔ G.rk p < i) ∧ p.1 ≠ G.m i :=
  Classical.choose_spec (G.exists_sample i) p hp

/-- Segment `s` crosses the sample line of strip `i`. -/
def spans (s : Sg) (i : ℕ) : Prop := s.1.1 < G.m i ∧ G.m i < s.2.1

theorem spans_iff {s : Sg} (hs : s ∈ G.S) (i : ℕ) :
    G.spans s i ↔ G.rk s.1 < i ∧ i ≤ G.rk s.2 := by
  have h1 := G.m_spec i (G.mem1 s hs)
  have h2 := G.m_spec i (G.mem2 s hs)
  unfold spans
  constructor
  · rintro ⟨a, b⟩
    refine ⟨h1.1.mp a, ?_⟩
    by_contra hc
    rw [not_le] at hc
    exact absurd (h2.1.mpr hc) (not_lt.mpr b.le)
  · rintro ⟨a, b⟩
    refine ⟨h1.1.mpr a, ?_⟩
    rcases lt_or_gt_of_ne h2.2 with h | h
    · exact absurd (h2.1.mp h) (not_lt.mpr b)
    · exact h

theorem rk_seg {s : Sg} (hs : s ∈ G.S) : G.rk s.1 < G.rk s.2 :=
  G.rk_lt_of_lt (G.mem1 s hs) (G.hor s hs)

/-- Distinct segments crossing a sample line have distinct heights there. -/
theorem hgt_ne {s t : Sg} (hs : s ∈ G.S) (ht : t ∈ G.S) (hst : s ≠ t) {i : ℕ}
    (hsi : G.spans s i) (hti : G.spans t i) : hgt s (G.m i) ≠ hgt t (G.m i) := by
  intro h
  have hq := G.disj s hs t ht hst (G.m i, hgt s (G.m i)) ⟨hsi.1.le, hsi.2.le, rfl⟩
    ⟨hti.1.le, hti.2.le, h⟩
  exact (G.m_spec i hq).2 rfl

/-! ## M3: the sweep gap graph and its component lower bound -/

open Classical in
/-- Segments crossing strip `i`. -/
noncomputable def sp (i : ℕ) : Finset Sg := G.S.filter (fun s => G.spans s i)

open Classical in
/-- Segments passing through event `r` (crossing strips `r` and `r+1`). -/
noncomputable def T (r : ℕ) : Finset Sg := G.S.filter (fun s => G.spans s r ∧ G.spans s (r + 1))

open Classical in
/-- Lowest element of `A` in strip `i` (by height at the sample line), if any. -/
noncomputable def low (i : ℕ) (A : Finset Sg) : Option Sg :=
  if h : A.Nonempty then some (Classical.choose (A.exists_min_image (fun s => hgt s (G.m i)) h))
  else none

/-- The event point of rank `r`. -/
noncomputable def ev (r : ℕ) : Pt := if h : ∃ w ∈ G.P, G.rk w = r then Classical.choose h else 0

open Classical in
/-- The gap just below the event point, seen from strip `r` / strip `r+1`. -/
noncomputable def loL (r : ℕ) : Option Sg :=
  G.low r ((G.sp r).filter (fun s => (G.ev r).2 ≤ hgt s (G.ev r).1))

open Classical in
noncomputable def loR (r : ℕ) : Option Sg :=
  G.low (r + 1) ((G.sp (r + 1)).filter (fun s => (G.ev r).2 ≤ hgt s (G.ev r).1))

open Classical in
/-- Gap nodes: `(i, none)` is the top gap of strip `i`, `(i, some s)` the gap just below `s`. -/
noncomputable def nodes : Finset (ℕ × Option Sg) :=
  (Finset.range (G.P.card + 1)).biUnion
    (fun i => insert (i, none) ((G.sp i).image (fun s => (i, some s))))

/-- Gap adjacency across event `r`: through gaps, plus one bottom pair. -/
def rel (a b : ℕ × Option Sg) : Prop :=
  ∃ r < G.P.card, a.1 = r ∧ b.1 = r + 1 ∧
    ((a.2 = b.2 ∧ (a.2 = none ∨ ∃ s ∈ G.T r, a.2 = some s)) ∨ (a.2 = G.loL r ∧ b.2 = G.loR r))

noncomputable def H : SimpleGraph {n // n ∈ G.nodes} :=
  SimpleGraph.fromRel (fun a b => G.rel a.1 b.1)

theorem card_nodes : G.nodes.card = ∑ i ∈ Finset.range (G.P.card + 1), ((G.sp i).card + 1) := by
  classical
  unfold nodes
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective]
    · intro a b hab
      simp only [Prod.mk.injEq, Option.some.injEq, true_and] at hab
      exact hab
    · simp only [Finset.mem_image, Prod.mk.injEq, reduceCtorEq, and_false, exists_false,
        not_false_eq_true]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_image] at hx hx'
    have e1 : x.1 = i := by
      rcases hx with rfl | ⟨s, _, rfl⟩ <;> rfl
    have e2 : x.1 = j := by
      rcases hx' with rfl | ⟨s, _, rfl⟩ <;> rfl
    exact hij (e1.symm.trans e2)

theorem sum_sp : ∑ i ∈ Finset.range (G.P.card + 1), (G.sp i).card
    = ∑ s ∈ G.S, (G.rk s.2 - G.rk s.1) := by
  classical
  simp only [sp, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.card_filter, ← Nat.card_Ioc]
  congr 1
  ext i
  have h2 := G.rk_lt_card (G.mem2 s hs)
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, G.spans_iff hs]
  omega

theorem sum_T : ∑ r ∈ Finset.range G.P.card, (G.T r).card
    = ∑ s ∈ G.S, (G.rk s.2 - G.rk s.1 - 1) := by
  classical
  simp only [T, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.card_filter, ← Nat.card_Ioo]
  congr 1
  ext i
  have h2 := G.rk_lt_card (G.mem2 s hs)
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo, G.spans_iff hs]
  omega

open Classical in
/-- All raw pairs that can be related across some event. -/
noncomputable def pairsQ : Finset ((ℕ × Option Sg) × (ℕ × Option Sg)) :=
  (Finset.range G.P.card).biUnion
    (fun r => insert ((r, G.loL r), (r + 1, G.loR r)) (insert ((r, none), (r + 1, none))
      ((G.T r).image (fun s => ((r, some s), (r + 1, some s))))))

theorem rel_mem_Q {a b : ℕ × Option Sg} (h : G.rel a b) : (a, b) ∈ G.pairsQ := by
  obtain ⟨r, hr, h1, h2, h3⟩ := h
  obtain ⟨i, g⟩ := a
  obtain ⟨j, g'⟩ := b
  simp only at h1 h2 h3
  subst h1 h2
  simp only [pairsQ, Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert, Finset.mem_image,
    Prod.mk.injEq]
  refine ⟨i, hr, ?_⟩
  rcases h3 with ⟨hgg, hg⟩ | ⟨hl, hr'⟩
  · subst hgg
    rcases hg with rfl | ⟨s, hs, rfl⟩
    · exact Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨s, hs, ⟨rfl, rfl⟩, rfl, rfl⟩)
  · exact Or.inl ⟨⟨rfl, hl⟩, rfl, hr'⟩

theorem card_Q : G.pairsQ.card ≤ ∑ r ∈ Finset.range G.P.card, ((G.T r).card + 2) := by
  classical
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun r _ => ?_)
  refine le_trans (Finset.card_insert_le _ _) ?_
  have := Finset.card_insert_le ((r, (none : Option Sg)), (r + 1, (none : Option Sg)))
    ((G.T r).image (fun s => ((r, some s), (r + 1, some s))))
  have := Finset.card_image_le (s := G.T r) (f := fun s => ((r, some s), (r + 1, some s)))
  omega

end SL

open Matrix in
/-- #components ≥ #vertices - #generating pairs (via the Laplacian kernel). -/
theorem card_le_pairs_add_components {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (R : Finset (α × α))
    (hR : ∀ i j, G.Adj i j → (i, j) ∈ R ∨ (j, i) ∈ R) :
    Fintype.card α ≤ R.card + Fintype.card G.ConnectedComponent := by
  rw [SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  let f : (α → ℝ) →ₗ[ℝ] (R → ℝ) :=
    { toFun := fun x r => x r.1.1 - x r.1.2
      map_add' := fun x y => by funext r; simp only [Pi.add_apply]; ring
      map_smul' := fun c x => by
        funext r; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hker : LinearMap.ker f ≤ LinearMap.ker (G.lapMatrix ℝ).toLin' := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [Matrix.toLin'_apply, SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj]
    intro i j hij
    rcases hR i j hij with h | h
    · have := congr_fun hx ⟨(i, j), h⟩
      simpa [f, sub_eq_zero] using this
    · have := congr_fun hx ⟨(j, i), h⟩
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, sub_eq_zero] at this
      exact this.symm
  have h1 := f.finrank_range_add_finrank_ker
  have h2 : Module.finrank ℝ (LinearMap.range f) ≤ R.card := by
    calc Module.finrank ℝ (LinearMap.range f) ≤ Module.finrank ℝ (R → ℝ) :=
          Submodule.finrank_le _
      _ = R.card := by simp
  have h3 := Submodule.finrank_mono hker
  simp only [Module.finrank_fintype_fun_eq_card] at h1
  omega

namespace SL
variable (G : SL)

/-- The sweep lower bound: `#components(H) ≥ 1 + |S| - |P|`. -/
theorem comp_lower : 1 + G.S.card ≤ G.P.card + Nat.card G.H.ConnectedComponent := by
  classical
  rw [Nat.card_eq_fintype_card]
  let R := (Finset.univ : Finset ({n // n ∈ G.nodes} × {n // n ∈ G.nodes})).filter
    (fun ab => G.rel ab.1.1 ab.2.1)
  have hR : ∀ a b : {n // n ∈ G.nodes}, G.H.Adj a b → (a, b) ∈ R ∨ (b, a) ∈ R := by
    intro a b hab
    rw [H, SimpleGraph.fromRel_adj] at hab
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hab.2
  have h1 := card_le_pairs_add_components G.H R hR
  rw [Fintype.card_coe] at h1
  have hQ : R.card ≤ G.pairsQ.card := by
    apply Finset.card_le_card_of_injOn (fun ab => (ab.1.1, ab.2.1))
    · intro ab hab
      rw [Finset.mem_coe, Finset.mem_filter] at hab
      exact Finset.mem_coe.mpr (G.rel_mem_Q hab.2)
    · intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (Subtype.ext hab.1) (Subtype.ext hab.2)
  have h2 := G.card_Q
  have h3 := G.card_nodes
  have h4 := G.sum_sp
  have h5 := G.sum_T
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h3
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
  have h6 : ∑ s ∈ G.S, (G.rk s.2 - G.rk s.1) =
      ∑ s ∈ G.S, (G.rk s.2 - G.rk s.1 - 1) + G.S.card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have := G.rk_seg hs
    omega
  omega

end SL


/-! ## M4a: events, the three order facts, lowest/highest, connectivity -/

namespace SL
variable (G : SL)

theorem exists_rank {r : ℕ} (hr : r < G.P.card) : ∃ w ∈ G.P, G.rk w = r := by
  classical
  have hsub : G.P.image G.rk ⊆ Finset.range G.P.card := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (G.rk_lt_card hp)
  have hcard : (G.P.image G.rk).card = G.P.card :=
    Finset.card_image_of_injOn (fun p hp q hq h => G.rk_inj hp hq h)
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have hmem : r ∈ G.P.image G.rk := by rw [heq]; exact Finset.mem_range.mpr hr
  obtain ⟨w, hw, h⟩ := Finset.mem_image.mp hmem
  exact ⟨w, hw, h⟩

theorem ev_spec {r : ℕ} (hr : r < G.P.card) : G.ev r ∈ G.P ∧ G.rk (G.ev r) = r := by
  have h := G.exists_rank hr
  unfold ev
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem ev_rk {w : Pt} (hw : w ∈ G.P) : G.ev (G.rk w) = w :=
  G.rk_inj (G.ev_spec (G.rk_lt_card hw)).1 hw (G.ev_spec (G.rk_lt_card hw)).2

theorem ev_lt {r : ℕ} (hr : r < G.P.card) : G.m r < (G.ev r).1 ∧ (G.ev r).1 < G.m (r + 1) := by
  obtain ⟨hw, hrk⟩ := G.ev_spec hr
  have h1 := G.m_spec r hw
  have h2 := G.m_spec (r + 1) hw
  refine ⟨?_, h2.1.mpr (by omega)⟩
  rcases lt_or_gt_of_ne h1.2 with h | h
  · exact absurd (h1.1.mp h) (by omega)
  · exact h

theorem gapL {r : ℕ} (hr : r < G.P.card) : ∀ p ∈ G.P, ¬ (G.m r < p.1 ∧ p.1 < (G.ev r).1) := by
  rintro p hp ⟨h1, h2⟩
  obtain ⟨hw, hrk⟩ := G.ev_spec hr
  have h4 := G.rk_lt_of_lt hp h2
  have h5 : ¬ p.1 < G.m r := not_lt.mpr h1.le
  rw [(G.m_spec r hp).1] at h5
  omega

theorem gapR {r : ℕ} (hr : r < G.P.card) :
    ∀ p ∈ G.P, ¬ ((G.ev r).1 < p.1 ∧ p.1 < G.m (r + 1)) := by
  rintro p hp ⟨h1, h2⟩
  obtain ⟨hw, hrk⟩ := G.ev_spec hr
  have h4 := G.rk_lt_of_lt hw h1
  have h5 := (G.m_spec (r + 1) hp).1.mp h2
  omega

open Classical in
/-- Segments ending at the event point (they cross strip `r` only near it). -/
noncomputable def Lf (r : ℕ) : Finset Sg := G.S.filter (fun s => s.2 = G.ev r)

open Classical in
/-- Segments starting at the event point. -/
noncomputable def Rt (r : ℕ) : Finset Sg := G.S.filter (fun s => s.1 = G.ev r)

open Classical in
/-- Through segments passing above the event point. -/
noncomputable def Tab (r : ℕ) : Finset Sg := (G.T r).filter (fun t => (G.ev r).2 < hgt t (G.ev r).1)

theorem mem_sp {i : ℕ} {s : Sg} : s ∈ G.sp i ↔ s ∈ G.S ∧ G.spans s i := by
  classical
  exact Finset.mem_filter

theorem mem_T {r : ℕ} {s : Sg} : s ∈ G.T r ↔ s ∈ G.S ∧ G.spans s r ∧ G.spans s (r + 1) := by
  classical
  exact Finset.mem_filter

theorem mem_Lf {r : ℕ} {s : Sg} : s ∈ G.Lf r ↔ s ∈ G.S ∧ s.2 = G.ev r := by
  classical
  exact Finset.mem_filter

theorem mem_Rt {r : ℕ} {s : Sg} : s ∈ G.Rt r ↔ s ∈ G.S ∧ s.1 = G.ev r := by
  classical
  exact Finset.mem_filter

theorem mem_Tab {r : ℕ} {s : Sg} : s ∈ G.Tab r ↔ s ∈ G.T r ∧ (G.ev r).2 < hgt s (G.ev r).1 := by
  classical
  exact Finset.mem_filter

theorem Lf_sp {r : ℕ} (hr : r < G.P.card) {s : Sg} (hs : s ∈ G.Lf r) : s ∈ G.sp r := by
  rw [mem_Lf] at hs
  rw [mem_sp, G.spans_iff hs.1]
  have h1 := G.rk_seg hs.1
  rw [hs.2, (G.ev_spec hr).2] at h1 ⊢
  exact ⟨hs.1, h1, le_refl r⟩

theorem Rt_sp {r : ℕ} (hr : r < G.P.card) {s : Sg} (hs : s ∈ G.Rt r) : s ∈ G.sp (r + 1) := by
  rw [mem_Rt] at hs
  rw [mem_sp, G.spans_iff hs.1]
  have h1 := G.rk_seg hs.1
  rw [hs.2, (G.ev_spec hr).2] at h1 ⊢
  exact ⟨hs.1, Nat.lt_succ_self r, h1⟩

theorem T_sp {r : ℕ} {s : Sg} (hs : s ∈ G.T r) : s ∈ G.sp r ∧ s ∈ G.sp (r + 1) := by
  rw [mem_T] at hs
  exact ⟨G.mem_sp.mpr ⟨hs.1, hs.2.1⟩, G.mem_sp.mpr ⟨hs.1, hs.2.2⟩⟩

theorem T_rk {r : ℕ} {s : Sg} (hs : s ∈ G.T r) : G.rk s.1 < r ∧ r + 1 ≤ G.rk s.2 := by
  rw [mem_T] at hs
  exact ⟨((G.spans_iff hs.1 r).mp hs.2.1).1, ((G.spans_iff hs.1 (r + 1)).mp hs.2.2).2⟩

theorem sp_cases {r : ℕ} (hr : r < G.P.card) {s : Sg} (hs : s ∈ G.sp r) :
    s ∈ G.T r ∨ s ∈ G.Lf r := by
  rw [mem_sp] at hs
  have h := (G.spans_iff hs.1 r).mp hs.2
  by_cases h2 : G.rk s.2 = r
  · right
    rw [mem_Lf]
    refine ⟨hs.1, G.rk_inj (G.mem2 s hs.1) (G.ev_spec hr).1 ?_⟩
    rw [h2, (G.ev_spec hr).2]
  · left
    rw [mem_T, G.spans_iff hs.1, G.spans_iff hs.1]
    exact ⟨hs.1, h, by omega, by omega⟩

theorem sp1_cases {r : ℕ} (hr : r < G.P.card) {s : Sg} (hs : s ∈ G.sp (r + 1)) :
    s ∈ G.T r ∨ s ∈ G.Rt r := by
  rw [mem_sp] at hs
  have h := (G.spans_iff hs.1 (r + 1)).mp hs.2
  by_cases h2 : G.rk s.1 = r
  · right
    rw [mem_Rt]
    refine ⟨hs.1, G.rk_inj (G.mem1 s hs.1) (G.ev_spec hr).1 ?_⟩
    rw [h2, (G.ev_spec hr).2]
  · left
    rw [mem_T, G.spans_iff hs.1, G.spans_iff hs.1]
    exact ⟨hs.1, by omega, by omega, h.2⟩

theorem T_ne_ev {r : ℕ} (hr : r < G.P.card) {t : Sg} (ht : t ∈ G.T r) :
    hgt t (G.ev r).1 ≠ (G.ev r).2 := by
  intro h
  obtain ⟨hts, h1, h2⟩ := G.mem_T.mp ht
  obtain ⟨hw, hrk⟩ := G.ev_spec hr
  have hb := G.ev_lt hr
  have hk := G.T_rk ht
  have hon : onSeg t (G.ev r) := ⟨by linarith [h1.1], by linarith [h2.2], h.symm⟩
  rcases G.avoid t hts _ hw hon with e | e
  · rw [e] at hrk; omega
  · rw [e] at hrk; omega

theorem T_T_ne {r : ℕ} (hr : r < G.P.card) {t t' : Sg} (ht : t ∈ G.T r) (ht' : t' ∈ G.T r)
    (hne : t ≠ t') : hgt t (G.ev r).1 ≠ hgt t' (G.ev r).1 := by
  intro h
  obtain ⟨hts, h1, h2⟩ := G.mem_T.mp ht
  obtain ⟨hts', h1', h2'⟩ := G.mem_T.mp ht'
  have hb := G.ev_lt hr
  have hq := G.disj t hts t' hts' hne ((G.ev r).1, hgt t (G.ev r).1)
    ⟨by simp only; linarith [h1.1], by simp only; linarith [h2.2], rfl⟩
    ⟨by simp only; linarith [h1'.1], by simp only; linarith [h2'.2], h⟩
  have e := G.xinj _ hq _ (G.ev_spec hr).1 rfl
  exact G.T_ne_ev hr ht (congrArg Prod.snd e)

/-- Order of two through segments: strip `r` agrees with the event line. -/
theorem T_T_L {r : ℕ} (hr : r < G.P.card) {t t' : Sg} (ht : t ∈ G.T r) (ht' : t' ∈ G.T r) :
    hgt t (G.m r) < hgt t' (G.m r) ↔ hgt t (G.ev r).1 < hgt t' (G.ev r).1 := by
  by_cases hne : t = t'
  · subst hne; simp only [lt_irrefl]
  obtain ⟨hts, h1, h2⟩ := G.mem_T.mp ht
  obtain ⟨hts', h1', h2'⟩ := G.mem_T.mp ht'
  have hb := G.ev_lt hr
  constructor
  · intro h
    exact lt_of_le_of_ne (G.persist hts hts' hne hb.1 h1.1.le (by linarith [h2.2]) h1'.1.le
      (by linarith [h2'.2]) (G.gapL hr) h) (G.T_T_ne hr ht ht' hne)
  · intro h
    by_contra hc
    have hc' : hgt t' (G.m r) < hgt t (G.m r) :=
      lt_of_le_of_ne (not_lt.mp hc) (G.hgt_ne hts' hts (Ne.symm hne) h1' h1)
    have := G.persist hts' hts (Ne.symm hne) hb.1 h1'.1.le (by linarith [h2'.2]) h1.1.le
      (by linarith [h2.2]) (G.gapL hr) hc'
    linarith

/-- Order of two through segments: the event line agrees with strip `r+1`. -/
theorem T_T_R {r : ℕ} (hr : r < G.P.card) {t t' : Sg} (ht : t ∈ G.T r) (ht' : t' ∈ G.T r) :
    hgt t (G.ev r).1 < hgt t' (G.ev r).1 ↔ hgt t (G.m (r + 1)) < hgt t' (G.m (r + 1)) := by
  by_cases hne : t = t'
  · subst hne; simp only [lt_irrefl]
  obtain ⟨hts, h1, h2⟩ := G.mem_T.mp ht
  obtain ⟨hts', h1', h2'⟩ := G.mem_T.mp ht'
  have hb := G.ev_lt hr
  constructor
  · intro h
    exact lt_of_le_of_ne (G.persist hts hts' hne hb.2 (by linarith [h1.1]) h2.2.le
      (by linarith [h1'.1]) h2'.2.le (G.gapR hr) h) (G.hgt_ne hts hts' hne h2 h2')
  · intro h
    by_contra hc
    have hc' : hgt t' (G.ev r).1 < hgt t (G.ev r).1 :=
      lt_of_le_of_ne (not_lt.mp hc) (G.T_T_ne hr ht' ht (Ne.symm hne))
    have := G.persist hts' hts (Ne.symm hne) hb.2 (by linarith [h1'.1]) h2'.2.le
      (by linarith [h1.1]) h2.2.le (G.gapR hr) hc'
    linarith

theorem T_T {r : ℕ} (hr : r < G.P.card) {t t' : Sg} (ht : t ∈ G.T r) (ht' : t' ∈ G.T r) :
    hgt t (G.m r) < hgt t' (G.m r) ↔ hgt t (G.m (r + 1)) < hgt t' (G.m (r + 1)) :=
  (G.T_T_L hr ht ht').trans (G.T_T_R hr ht ht')

theorem Lf_hgt {r : ℕ} {l : Sg} (hl : l ∈ G.Lf r) :
    hgt l (G.ev r).1 = (G.ev r).2 := by
  rw [mem_Lf] at hl
  rw [← hl.2]
  exact hgt_snd l (G.hor l hl.1)

theorem Rt_hgt {r : ℕ} {q : Sg} (hq : q ∈ G.Rt r) : hgt q (G.ev r).1 = (G.ev r).2 := by
  rw [mem_Rt] at hq
  rw [← hq.2]
  exact hgt_fst q

theorem Lf_ne_T {r : ℕ} (hr : r < G.P.card) {l t : Sg} (hl : l ∈ G.Lf r) (ht : t ∈ G.T r) :
    l ≠ t := by
  intro e
  have h1 := (G.mem_Lf.mp hl).2
  have h2 := G.T_rk ht
  rw [← e, h1, (G.ev_spec hr).2] at h2
  omega

theorem Rt_ne_T {r : ℕ} (hr : r < G.P.card) {q t : Sg} (hq : q ∈ G.Rt r) (ht : t ∈ G.T r) :
    q ≠ t := by
  intro e
  have h1 := (G.mem_Rt.mp hq).2
  have h2 := G.T_rk ht
  rw [e] at h1
  rw [h1, (G.ev_spec hr).2] at h2
  omega

/-- A segment ending at the event point is below a through segment iff the latter passes above. -/
theorem Lf_T {r : ℕ} (hr : r < G.P.card) {l t : Sg} (hl : l ∈ G.Lf r) (ht : t ∈ G.T r) :
    hgt l (G.m r) < hgt t (G.m r) ↔ (G.ev r).2 < hgt t (G.ev r).1 := by
  have hne := G.Lf_ne_T hr hl ht
  obtain ⟨hls, hl1⟩ := G.mem_sp.mp (G.Lf_sp hr hl)
  obtain ⟨hts, h1, h2⟩ := G.mem_T.mp ht
  have hb := G.ev_lt hr
  have hle : (G.ev r).1 ≤ l.2.1 := by rw [(G.mem_Lf.mp hl).2]
  have hlh := G.Lf_hgt hl
  constructor
  · intro h
    have := G.persist hls hts hne hb.1 hl1.1.le hle h1.1.le (by linarith [h2.2]) (G.gapL hr) h
    exact lt_of_le_of_ne (by linarith) (Ne.symm (G.T_ne_ev hr ht))
  · intro h
    by_contra hc
    have hc' : hgt t (G.m r) < hgt l (G.m r) :=
      lt_of_le_of_ne (not_lt.mp hc) (G.hgt_ne hts hls (Ne.symm hne) h1 hl1)
    have := G.persist hts hls (Ne.symm hne) hb.1 h1.1.le (by linarith [h2.2]) hl1.1.le hle
      (G.gapL hr) hc'
    linarith

/-- A segment starting at the event point is below a through segment iff the latter passes above. -/
theorem Rt_T {r : ℕ} (hr : r < G.P.card) {q t : Sg} (hq : q ∈ G.Rt r) (ht : t ∈ G.T r) :
    hgt q (G.m (r + 1)) < hgt t (G.m (r + 1)) ↔ (G.ev r).2 < hgt t (G.ev r).1 := by
  have hne := G.Rt_ne_T hr hq ht
  obtain ⟨hqs, hq1⟩ := G.mem_sp.mp (G.Rt_sp hr hq)
  obtain ⟨hts, h1, h2⟩ := G.mem_T.mp ht
  have hb := G.ev_lt hr
  have hle : q.1.1 ≤ (G.ev r).1 := by rw [(G.mem_Rt.mp hq).2]
  have hqh := G.Rt_hgt hq
  constructor
  · intro h
    by_contra hc
    have hc' : hgt t (G.ev r).1 < hgt q (G.ev r).1 := by
      rw [hqh]; exact lt_of_le_of_ne (not_lt.mp hc) (G.T_ne_ev hr ht)
    have := G.persist hts hqs (Ne.symm hne) hb.2 (by linarith [h1.1]) h2.2.le hle hq1.2.le
      (G.gapR hr) hc'
    linarith
  · intro h
    have h' : hgt q (G.ev r).1 < hgt t (G.ev r).1 := by rw [hqh]; exact h
    exact lt_of_le_of_ne (G.persist hqs hts hne hb.2 hle hq1.2.le (by linarith [h1.1]) h2.2.le
      (G.gapR hr) h') (G.hgt_ne hqs hts hne hq1 h2)

/-! ### lowest / highest -/

theorem low_some {i : ℕ} {A : Finset Sg} {t : Sg} (h : G.low i A = some t) :
    t ∈ A ∧ ∀ t' ∈ A, hgt t (G.m i) ≤ hgt t' (G.m i) := by
  unfold low at h
  by_cases hA : A.Nonempty
  · rw [dif_pos hA, Option.some.injEq] at h
    subst h
    exact Classical.choose_spec (A.exists_min_image (fun s => hgt s (G.m i)) hA)
  · rw [dif_neg hA] at h
    simp at h

theorem low_none {i : ℕ} {A : Finset Sg} (h : G.low i A = none) : A = ∅ := by
  unfold low at h
  by_cases hA : A.Nonempty
  · rw [dif_pos hA] at h
    simp at h
  · exact Finset.not_nonempty_iff_eq_empty.mp hA

theorem low_empty (i : ℕ) : G.low i ∅ = none := by
  unfold low
  rw [dif_neg Finset.not_nonempty_empty]

theorem low_isSome {i : ℕ} {A : Finset Sg} (hA : A.Nonempty) : ∃ t, G.low i A = some t :=
  ⟨_, by unfold low; rw [dif_pos hA]⟩

theorem low_eq {i : ℕ} {A : Finset Sg} {t : Sg} (ht : t ∈ A)
    (hmin : ∀ t' ∈ A, t' ≠ t → hgt t (G.m i) < hgt t' (G.m i)) : G.low i A = some t := by
  obtain ⟨c, hc⟩ := G.low_isSome (i := i) ⟨t, ht⟩
  obtain ⟨hcA, hcmin⟩ := G.low_some hc
  rw [hc]
  by_contra hne
  have hne' : c ≠ t := fun e => hne (by rw [e])
  have h1 := hmin c hcA hne'
  have h2 := hcmin t ht
  linarith

theorem low_strict {i : ℕ} {A : Finset Sg} {t : Sg} (hA : A ⊆ G.sp i) (h : G.low i A = some t) :
    ∀ t' ∈ A, t' ≠ t → hgt t (G.m i) < hgt t' (G.m i) := by
  obtain ⟨htA, hmin⟩ := G.low_some h
  intro t' ht' hne
  have h1 := G.mem_sp.mp (hA htA)
  have h2 := G.mem_sp.mp (hA ht')
  exact lt_of_le_of_ne (hmin t' ht') (G.hgt_ne h1.1 h2.1 (Ne.symm hne) h1.2 h2.2)

theorem low_transfer {i j : ℕ} {A : Finset Sg} (hAi : A ⊆ G.sp i)
    (hord : ∀ a ∈ A, ∀ b ∈ A, hgt a (G.m i) < hgt b (G.m i) → hgt a (G.m j) < hgt b (G.m j)) :
    G.low i A = G.low j A := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · rw [hA, low_empty, low_empty]
  · obtain ⟨t, ht⟩ := G.low_isSome (i := i) hA
    rw [ht, eq_comm]
    exact G.low_eq (G.low_some ht).1
      (fun t' h' hne => hord t (G.low_some ht).1 t' h' (G.low_strict hAi ht t' h' hne))

open Classical in
theorem low_union {i : ℕ} {A B : Finset Sg} (hA : A ⊆ G.sp i) {a : Sg} (ha : a ∈ A)
    (hab : ∀ b ∈ B, hgt a (G.m i) < hgt b (G.m i)) : G.low i (A ∪ B) = G.low i A := by
  obtain ⟨t, ht⟩ := G.low_isSome (i := i) ⟨a, ha⟩
  rw [ht]
  obtain ⟨htA, hmin⟩ := G.low_some ht
  apply G.low_eq (Finset.mem_union_left _ htA)
  intro t' h' hne
  rcases Finset.mem_union.mp h' with h' | h'
  · exact G.low_strict hA ht t' h' hne
  · have := hmin a ha
    have := hab t' h'
    linarith

open Classical in
/-- Highest element of `A` in strip `i`, if any. -/
noncomputable def high (i : ℕ) (A : Finset Sg) : Option Sg :=
  if h : A.Nonempty then some (Classical.choose (A.exists_max_image (fun s => hgt s (G.m i)) h))
  else none

theorem high_some {i : ℕ} {A : Finset Sg} {t : Sg} (h : G.high i A = some t) :
    t ∈ A ∧ ∀ t' ∈ A, hgt t' (G.m i) ≤ hgt t (G.m i) := by
  unfold high at h
  by_cases hA : A.Nonempty
  · rw [dif_pos hA, Option.some.injEq] at h
    subst h
    exact Classical.choose_spec (A.exists_max_image (fun s => hgt s (G.m i)) hA)
  · rw [dif_neg hA] at h
    simp at h

theorem high_none {i : ℕ} {A : Finset Sg} (h : G.high i A = none) : A = ∅ := by
  unfold high at h
  by_cases hA : A.Nonempty
  · rw [dif_pos hA] at h
    simp at h
  · exact Finset.not_nonempty_iff_eq_empty.mp hA

theorem high_isSome {i : ℕ} {A : Finset Sg} (hA : A.Nonempty) : ∃ t, G.high i A = some t :=
  ⟨_, by unfold high; rw [dif_pos hA]⟩

/-! ### gap-graph connectivity on raw nodes -/

/-- Two raw gap nodes are nodes of `H` and connected in `H`. -/
def Conn (a b : ℕ × Option Sg) : Prop :=
  ∃ (ha : a ∈ G.nodes) (hb : b ∈ G.nodes), G.H.Reachable ⟨a, ha⟩ ⟨b, hb⟩

theorem conn_refl {a : ℕ × Option Sg} (ha : a ∈ G.nodes) : G.Conn a a :=
  ⟨ha, ha, SimpleGraph.Reachable.refl _⟩

theorem conn_symm {a b : ℕ × Option Sg} (h : G.Conn a b) : G.Conn b a :=
  let ⟨ha, hb, h⟩ := h
  ⟨hb, ha, h.symm⟩

theorem conn_trans {a b c : ℕ × Option Sg} (h1 : G.Conn a b) (h2 : G.Conn b c) : G.Conn a c :=
  let ⟨ha, _, h⟩ := h1
  let ⟨_, hc, h'⟩ := h2
  ⟨ha, hc, h.trans h'⟩

theorem conn_rel {a b : ℕ × Option Sg} (ha : a ∈ G.nodes) (hb : b ∈ G.nodes) (h : G.rel a b) :
    G.Conn a b := by
  refine ⟨ha, hb, ?_⟩
  by_cases hab : a = b
  · subst hab
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    rw [H, SimpleGraph.fromRel_adj]
    exact ⟨fun e => hab (congrArg Subtype.val e), Or.inl h⟩

theorem mem_nodes {i : ℕ} {g : Option Sg} :
    (i, g) ∈ G.nodes ↔ i ≤ G.P.card ∧ ∀ s, g = some s → s ∈ G.sp i := by
  classical
  unfold nodes
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [Finset.mem_range] at hj
    rw [Finset.mem_insert, Finset.mem_image] at h
    rcases h with h | ⟨s, hs, h⟩
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, fun s h => by simp at h⟩
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by omega, fun s' h => ?_⟩
      rw [Option.some.injEq] at h
      rw [← h]
      exact hs
  · rintro ⟨hi, hg⟩
    refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Finset.mem_insert, Finset.mem_image]
    cases g with
    | none => exact Or.inl rfl
    | some s => exact Or.inr ⟨s, hg s rfl, rfl⟩

theorem node_low {i : ℕ} (hi : i ≤ G.P.card) {A : Finset Sg} (hA : A ⊆ G.sp i) :
    (i, G.low i A) ∈ G.nodes :=
  G.mem_nodes.mpr ⟨hi, fun _ h => hA (G.low_some h).1⟩

theorem node_some {i : ℕ} (hi : i ≤ G.P.card) {s : Sg} (hs : s ∈ G.sp i) :
    (i, some s) ∈ G.nodes :=
  G.mem_nodes.mpr ⟨hi, fun _ h => by rw [Option.some.injEq] at h; rw [← h]; exact hs⟩

theorem rel_through {r : ℕ} (hr : r < G.P.card) {g : Option Sg}
    (hg : ∀ s, g = some s → s ∈ G.T r) : G.rel (r, g) (r + 1, g) := by
  refine ⟨r, hr, rfl, rfl, Or.inl ⟨rfl, ?_⟩⟩
  cases g with
  | none => exact Or.inl rfl
  | some s => exact Or.inr ⟨s, hg s rfl, rfl⟩

theorem rel_bottom {r : ℕ} (hr : r < G.P.card) : G.rel (r, G.loL r) (r + 1, G.loR r) :=
  ⟨r, hr, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

end SL

/-! ## M4b: successor gaps, the rotation `ncw`, the wedge lemma, continuity along segments -/

namespace SL
variable (G : SL)

open Classical in
/-- The gap directly above `s` in strip `i` is the gap below `succ i s`. -/
noncomputable def succ (i : ℕ) (s : Sg) : Option Sg :=
  G.low i ((G.sp i).filter (fun t => hgt s (G.m i) < hgt t (G.m i)))

theorem node_succ {i : ℕ} (hi : i ≤ G.P.card) (s : Sg) : (i, G.succ i s) ∈ G.nodes :=
  G.node_low hi (Finset.filter_subset _ _)

theorem node_loL {r : ℕ} (hr : r < G.P.card) : (r, G.loL r) ∈ G.nodes :=
  G.node_low hr.le (Finset.filter_subset _ _)

theorem node_loR {r : ℕ} (hr : r < G.P.card) : (r + 1, G.loR r) ∈ G.nodes :=
  G.node_low hr (Finset.filter_subset _ _)

theorem Tab_sp {r : ℕ} : G.Tab r ⊆ G.sp r := fun _ ht => (G.T_sp (G.mem_Tab.mp ht).1).1

theorem Tab_sp1 {r : ℕ} : G.Tab r ⊆ G.sp (r + 1) := fun _ ht => (G.T_sp (G.mem_Tab.mp ht).1).2

theorem Rt_snd {r : ℕ} {s : Sg} (hs : s ∈ G.Rt r) : s.2 ≠ G.ev r := by
  intro h
  obtain ⟨hs1, hs2⟩ := G.mem_Rt.mp hs
  have := G.hor s hs1
  rw [hs2, ← h] at this
  exact lt_irrefl _ this

theorem Lf_fst {r : ℕ} {s : Sg} (hs : s ∈ G.Lf r) : s.1 ≠ G.ev r := by
  intro h
  obtain ⟨hs1, hs2⟩ := G.mem_Lf.mp hs
  have := G.hor s hs1
  rw [hs2, ← h] at this
  exact lt_irrefl _ this

open Classical in
theorem FL_eq {r : ℕ} (hr : r < G.P.card) :
    (G.sp r).filter (fun s => (G.ev r).2 ≤ hgt s (G.ev r).1) = G.Lf r ∪ G.Tab r := by
  ext t
  rw [Finset.mem_filter, Finset.mem_union, G.mem_Tab]
  constructor
  · rintro ⟨h1, h2⟩
    rcases G.sp_cases hr h1 with h | h
    · exact Or.inr ⟨h, lt_of_le_of_ne h2 (Ne.symm (G.T_ne_ev hr h))⟩
    · exact Or.inl h
  · rintro (h | h)
    · exact ⟨G.Lf_sp hr h, le_of_eq (G.Lf_hgt h).symm⟩
    · exact ⟨(G.T_sp h.1).1, h.2.le⟩

open Classical in
theorem FR_eq {r : ℕ} (hr : r < G.P.card) :
    (G.sp (r + 1)).filter (fun s => (G.ev r).2 ≤ hgt s (G.ev r).1) = G.Rt r ∪ G.Tab r := by
  ext t
  rw [Finset.mem_filter, Finset.mem_union, G.mem_Tab]
  constructor
  · rintro ⟨h1, h2⟩
    rcases G.sp1_cases hr h1 with h | h
    · exact Or.inr ⟨h, lt_of_le_of_ne h2 (Ne.symm (G.T_ne_ev hr h))⟩
    · exact Or.inl h
  · rintro (h | h)
    · exact ⟨G.Rt_sp hr h, le_of_eq (G.Rt_hgt h).symm⟩
    · exact ⟨(G.T_sp h.1).2, h.2.le⟩

open Classical in
theorem loL_eq {r : ℕ} (hr : r < G.P.card) : G.loL r = G.low r (G.Lf r ∪ G.Tab r) := by
  unfold loL
  rw [G.FL_eq hr]

open Classical in
theorem loR_eq {r : ℕ} (hr : r < G.P.card) : G.loR r = G.low (r + 1) (G.Rt r ∪ G.Tab r) := by
  unfold loR
  rw [G.FR_eq hr]

theorem loL_Lf {r : ℕ} (hr : r < G.P.card) {l : Sg} (hl : l ∈ G.Lf r) :
    G.loL r = G.low r (G.Lf r) := by
  rw [G.loL_eq hr]
  exact G.low_union (fun _ hx => G.Lf_sp hr hx) hl
    (fun b hb => (G.Lf_T hr hl (G.mem_Tab.mp hb).1).mpr (G.mem_Tab.mp hb).2)

theorem loR_Rt {r : ℕ} (hr : r < G.P.card) {q : Sg} (hq : q ∈ G.Rt r) :
    G.loR r = G.low (r + 1) (G.Rt r) := by
  rw [G.loR_eq hr]
  exact G.low_union (fun _ hx => G.Rt_sp hr hx) hq
    (fun b hb => (G.Rt_T hr hq (G.mem_Tab.mp hb).1).mpr (G.mem_Tab.mp hb).2)

theorem loL_nil {r : ℕ} (hr : r < G.P.card) (h : G.Lf r = ∅) : G.loL r = G.low r (G.Tab r) := by
  rw [G.loL_eq hr, h, Finset.empty_union]

theorem loR_nil {r : ℕ} (hr : r < G.P.card) (h : G.Rt r = ∅) :
    G.loR r = G.low (r + 1) (G.Tab r) := by
  rw [G.loR_eq hr, h, Finset.empty_union]

theorem Tstar {r : ℕ} (hr : r < G.P.card) : G.low (r + 1) (G.Tab r) = G.low r (G.Tab r) :=
  G.low_transfer (G.Tab_sp1) (fun _ ha _ hb h =>
    (G.T_T hr (G.mem_Tab.mp ha).1 (G.mem_Tab.mp hb).1).mpr h)

theorem conn_through_Tab {r : ℕ} (hr : r < G.P.card) :
    G.Conn (r, G.low r (G.Tab r)) (r + 1, G.low r (G.Tab r)) :=
  G.conn_rel (G.node_low hr.le G.Tab_sp) (by rw [← G.Tstar hr]; exact G.node_low hr G.Tab_sp1)
    (G.rel_through hr (fun _ ht => (G.mem_Tab.mp (G.low_some ht).1).1))

theorem succ_Lf_top {r : ℕ} (hr : r < G.P.card) {l : Sg} (hl : l ∈ G.Lf r)
    (htop : ∀ l' ∈ G.Lf r, ¬ hgt l (G.m r) < hgt l' (G.m r)) :
    G.succ r l = G.low r (G.Tab r) := by
  unfold succ
  congr 1
  ext t
  rw [Finset.mem_filter, G.mem_Tab]
  constructor
  · rintro ⟨h1, h2⟩
    rcases G.sp_cases hr h1 with h | h
    · exact ⟨h, (G.Lf_T hr hl h).mp h2⟩
    · exact absurd h2 (htop t h)
  · rintro ⟨h1, h2⟩
    exact ⟨(G.T_sp h1).1, (G.Lf_T hr hl h1).mpr h2⟩

theorem succ_Rt_top {r : ℕ} (hr : r < G.P.card) {q : Sg} (hq : q ∈ G.Rt r)
    (htop : ∀ q' ∈ G.Rt r, ¬ hgt q (G.m (r + 1)) < hgt q' (G.m (r + 1))) :
    G.succ (r + 1) q = G.low r (G.Tab r) := by
  rw [← G.Tstar hr]
  unfold succ
  congr 1
  ext t
  rw [Finset.mem_filter, G.mem_Tab]
  constructor
  · rintro ⟨h1, h2⟩
    rcases G.sp1_cases hr h1 with h | h
    · exact ⟨h, (G.Rt_T hr hq h).mp h2⟩
    · exact absurd h2 (htop t h)
  · rintro ⟨h1, h2⟩
    exact ⟨(G.T_sp h1).2, (G.Rt_T hr hq h1).mpr h2⟩

theorem succ_Rt_next {r : ℕ} (hr : r < G.P.card) {q s : Sg} (hq : q ∈ G.Rt r) (hs : s ∈ G.Rt r)
    (hlt : hgt q (G.m (r + 1)) < hgt s (G.m (r + 1)))
    (hbtw : ∀ q' ∈ G.Rt r, hgt q (G.m (r + 1)) < hgt q' (G.m (r + 1)) →
      hgt s (G.m (r + 1)) ≤ hgt q' (G.m (r + 1))) :
    G.succ (r + 1) q = some s := by
  unfold succ
  apply G.low_eq
  · rw [Finset.mem_filter]
    exact ⟨G.Rt_sp hr hs, hlt⟩
  · intro t ht hne
    rw [Finset.mem_filter] at ht
    rcases G.sp1_cases hr ht.1 with h | h
    · exact (G.Rt_T hr hs h).mpr ((G.Rt_T hr hq h).mp ht.2)
    · have h1 := G.mem_sp.mp (G.Rt_sp hr hs)
      have h2 := G.mem_sp.mp ht.1
      exact lt_of_le_of_ne (hbtw t h ht.2) (G.hgt_ne h1.1 h2.1 (Ne.symm hne) h1.2 h2.2)

theorem succ_Lf_next {r : ℕ} (hr : r < G.P.card) {s l : Sg} (hs : s ∈ G.Lf r) (hl : l ∈ G.Lf r)
    (hlt : hgt s (G.m r) < hgt l (G.m r))
    (hbtw : ∀ l' ∈ G.Lf r, hgt s (G.m r) < hgt l' (G.m r) → hgt l (G.m r) ≤ hgt l' (G.m r)) :
    G.succ r s = some l := by
  unfold succ
  apply G.low_eq
  · rw [Finset.mem_filter]
    exact ⟨G.Lf_sp hr hl, hlt⟩
  · intro t ht hne
    rw [Finset.mem_filter] at ht
    rcases G.sp_cases hr ht.1 with h | h
    · exact (G.Lf_T hr hl h).mpr ((G.Lf_T hr hs h).mp ht.2)
    · have h1 := G.mem_sp.mp (G.Lf_sp hr hl)
      have h2 := G.mem_sp.mp ht.1
      exact lt_of_le_of_ne (hbtw t h ht.2) (G.hgt_ne h1.1 h2.1 (Ne.symm hne) h1.2 h2.2)

theorem low_Rt_bot {r : ℕ} (hr : r < G.P.card) {s : Sg} (hs : s ∈ G.Rt r)
    (hbot : ∀ q' ∈ G.Rt r, ¬ hgt q' (G.m (r + 1)) < hgt s (G.m (r + 1))) :
    G.low (r + 1) (G.Rt r) = some s := by
  apply G.low_eq hs
  intro t ht hne
  have h1 := G.mem_sp.mp (G.Rt_sp hr hs)
  have h2 := G.mem_sp.mp (G.Rt_sp hr ht)
  exact lt_of_le_of_ne (not_lt.mp (hbot t ht)) (G.hgt_ne h1.1 h2.1 (Ne.symm hne) h1.2 h2.2)

open Classical in
noncomputable def Rbelow (r : ℕ) (s : Sg) : Finset Sg :=
  (G.Rt r).filter (fun q => hgt q (G.m (r + 1)) < hgt s (G.m (r + 1)))

open Classical in
noncomputable def Labove (r : ℕ) (s : Sg) : Finset Sg :=
  (G.Lf r).filter (fun l => hgt s (G.m r) < hgt l (G.m r))

open Classical in
/-- Next segment clockwise around the event point `ev r` after `s`. Clockwise order at `w`:
segments starting at `w` from top to bottom, then segments ending at `w` from bottom to top. -/
noncomputable def ncw (r : ℕ) (s : Sg) : Sg :=
  if s.1 = G.ev r then
    (G.high (r + 1) (G.Rbelow r s)).getD
      ((G.low r (G.Lf r)).getD ((G.high (r + 1) (G.Rt r)).getD s))
  else
    (G.low r (G.Labove r s)).getD
      ((G.high (r + 1) (G.Rt r)).getD ((G.low r (G.Lf r)).getD s))

open Classical in
/-- Left-side gap of the dart arriving at `ev r` along `s` (strip adjacent to the event). -/
noncomputable def arr (r : ℕ) (s : Sg) : ℕ × Option Sg :=
  if s.2 = G.ev r then (r, G.succ r s) else (r + 1, some s)

open Classical in
/-- Left-side gap of the dart leaving `ev r` along `b` (strip adjacent to the event). -/
noncomputable def lv (r : ℕ) (b : Sg) : ℕ × Option Sg :=
  if b.1 = G.ev r then (r + 1, G.succ (r + 1) b) else (r, some b)

theorem mem_Rbelow {r : ℕ} {s q : Sg} :
    q ∈ G.Rbelow r s ↔ q ∈ G.Rt r ∧ hgt q (G.m (r + 1)) < hgt s (G.m (r + 1)) := by
  classical
  exact Finset.mem_filter

theorem mem_Labove {r : ℕ} {s l : Sg} :
    l ∈ G.Labove r s ↔ l ∈ G.Lf r ∧ hgt s (G.m r) < hgt l (G.m r) := by
  classical
  exact Finset.mem_filter

theorem wedge_R {r : ℕ} (hr : r < G.P.card) {s : Sg} (hs : s ∈ G.Rt r) :
    G.Conn (G.arr r s) (G.lv r (G.ncw r s)) := by
  have hs1 := (G.mem_Rt.mp hs).2
  have harr : G.arr r s = (r + 1, some s) := by unfold arr; rw [if_neg (G.Rt_snd hs)]
  rw [harr]
  unfold ncw
  rw [if_pos hs1]
  rcases hRb : G.high (r + 1) (G.Rbelow r s) with _ | β
  · have hbot : ∀ q' ∈ G.Rt r, ¬ hgt q' (G.m (r + 1)) < hgt s (G.m (r + 1)) := by
      intro q' hq' hlt
      have h := G.mem_Rbelow.mpr ⟨hq', hlt⟩
      rw [G.high_none hRb] at h
      exact Finset.notMem_empty _ h
    have hloR : G.low (r + 1) (G.Rt r) = some s := G.low_Rt_bot hr hs hbot
    rw [Option.getD_none]
    rcases hL : G.low r (G.Lf r) with _ | β
    · have hLe := G.low_none hL
      obtain ⟨β, hβ⟩ := G.high_isSome (i := r + 1) ⟨s, hs⟩
      rw [Option.getD_none, hβ, Option.getD_some]
      obtain ⟨hβR, hβmax⟩ := G.high_some hβ
      have hlv : G.lv r β = (r + 1, G.low r (G.Tab r)) := by
        unfold lv
        rw [if_pos (G.mem_Rt.mp hβR).2,
          G.succ_Rt_top hr hβR (fun q' hq' h => absurd (hβmax q' hq') (not_le.mpr h))]
      rw [hlv]
      have hb : G.Conn (r, G.low r (G.Tab r)) (r + 1, some s) := by
        have h := G.rel_bottom hr
        rw [G.loL_nil hr hLe, G.loR_Rt hr hs, hloR] at h
        exact G.conn_rel (G.node_low hr.le G.Tab_sp) (G.node_some hr (G.Rt_sp hr hs)) h
      exact G.conn_trans (G.conn_symm hb) (G.conn_through_Tab hr)
    · rw [Option.getD_some]
      obtain ⟨hβL, _⟩ := G.low_some hL
      have hlv : G.lv r β = (r, some β) := by unfold lv; rw [if_neg (G.Lf_fst hβL)]
      rw [hlv]
      have h := G.rel_bottom hr
      rw [G.loL_Lf hr hβL, hL, G.loR_Rt hr hs, hloR] at h
      exact G.conn_symm (G.conn_rel (G.node_some hr.le (G.Lf_sp hr hβL))
        (G.node_some hr (G.Rt_sp hr hs)) h)
  · rw [Option.getD_some]
    obtain ⟨hβB, hβmax⟩ := G.high_some hRb
    have hβB' := G.mem_Rbelow.mp hβB
    have hlv : G.lv r β = (r + 1, some s) := by
      unfold lv
      rw [if_pos (G.mem_Rt.mp hβB'.1).2]
      congr 1
      apply G.succ_Rt_next hr hβB'.1 hs hβB'.2
      intro q' hq' hlt
      by_contra hc
      rw [not_le] at hc
      have := hβmax q' (G.mem_Rbelow.mpr ⟨hq', hc⟩)
      linarith
    rw [hlv]
    exact G.conn_refl (G.node_some hr (G.Rt_sp hr hs))

theorem wedge_L {r : ℕ} (hr : r < G.P.card) {s : Sg} (hs : s ∈ G.Lf r) :
    G.Conn (G.arr r s) (G.lv r (G.ncw r s)) := by
  have hs2 := (G.mem_Lf.mp hs).2
  have harr : G.arr r s = (r, G.succ r s) := by unfold arr; rw [if_pos hs2]
  rw [harr]
  unfold ncw
  rw [if_neg (G.Lf_fst hs)]
  rcases hLa : G.low r (G.Labove r s) with _ | β
  · have htop : ∀ l' ∈ G.Lf r, ¬ hgt s (G.m r) < hgt l' (G.m r) := by
      intro l' hl' hlt
      have h := G.mem_Labove.mpr ⟨hl', hlt⟩
      rw [G.low_none hLa] at h
      exact Finset.notMem_empty _ h
    rw [G.succ_Lf_top hr hs htop, Option.getD_none]
    rcases hR : G.high (r + 1) (G.Rt r) with _ | β
    · have hRe := G.high_none hR
      obtain ⟨β, hβ⟩ := G.low_isSome (i := r) ⟨s, hs⟩
      rw [Option.getD_none, hβ, Option.getD_some]
      obtain ⟨hβL, _⟩ := G.low_some hβ
      have hlv : G.lv r β = (r, some β) := by unfold lv; rw [if_neg (G.Lf_fst hβL)]
      rw [hlv]
      have hb : G.Conn (r, some β) (r + 1, G.low r (G.Tab r)) := by
        have h := G.rel_bottom hr
        rw [G.loL_Lf hr hβL, hβ, G.loR_nil hr hRe, G.Tstar hr] at h
        exact G.conn_rel (G.node_some hr.le (G.Lf_sp hr hβL))
          (by rw [← G.Tstar hr]; exact G.node_low hr G.Tab_sp1) h
      exact G.conn_trans (G.conn_through_Tab hr) (G.conn_symm hb)
    · rw [Option.getD_some]
      obtain ⟨hβR, hβmax⟩ := G.high_some hR
      have hlv : G.lv r β = (r + 1, G.low r (G.Tab r)) := by
        unfold lv
        rw [if_pos (G.mem_Rt.mp hβR).2,
          G.succ_Rt_top hr hβR (fun q' hq' h => absurd (hβmax q' hq') (not_le.mpr h))]
      rw [hlv]
      exact G.conn_through_Tab hr
  · rw [Option.getD_some]
    obtain ⟨hβA, hβmin⟩ := G.low_some hLa
    have hβA' := G.mem_Labove.mp hβA
    have hlv : G.lv r β = (r, some β) := by unfold lv; rw [if_neg (G.Lf_fst hβA'.1)]
    have hsu : G.succ r s = some β := by
      apply G.succ_Lf_next hr hs hβA'.1 hβA'.2
      intro l' hl' hlt
      by_contra hc
      rw [not_le] at hc
      have := hβmin l' (G.mem_Labove.mpr ⟨hl', hlt⟩)
      linarith
    rw [hlv, hsu]
    exact G.conn_refl (G.node_some hr.le (G.Lf_sp hr hβA'.1))

/-- The wedge lemma: the face on the left is continued across every event point. -/
theorem wedge {r : ℕ} (hr : r < G.P.card) {s : Sg} (hs : s ∈ G.Rt r ∨ s ∈ G.Lf r) :
    G.Conn (G.arr r s) (G.lv r (G.ncw r s)) := by
  rcases hs with hs | hs
  · exact G.wedge_R hr hs
  · exact G.wedge_L hr hs

theorem along_below {i : ℕ} (hi : i < G.P.card) {s : Sg} (hs : s ∈ G.T i) :
    G.Conn (i, some s) (i + 1, some s) :=
  G.conn_rel (G.node_some hi.le (G.T_sp hs).1) (G.node_some hi (G.T_sp hs).2)
    (G.rel_through hi (fun t ht => by rw [Option.some.injEq] at ht; rw [← ht]; exact hs))

/-- A through segment below every other one... (general case): the gap above `s` continues. -/
theorem along_above {i : ℕ} (hi : i < G.P.card) {s : Sg} (hs : s ∈ G.T i) :
    G.Conn (i, G.succ i s) (i + 1, G.succ (i + 1) s) := by
  classical
  have hsS := (G.mem_T.mp hs).1
  -- Lf elements vs s, Rt elements vs s
  have hLs : ∀ l ∈ G.Lf i, hgt l (G.m i) < hgt s (G.m i) ↔ (G.ev i).2 < hgt s (G.ev i).1 :=
    fun l hl => G.Lf_T hi hl hs
  have hRs : ∀ q ∈ G.Rt i, hgt q (G.m (i + 1)) < hgt s (G.m (i + 1)) ↔
      (G.ev i).2 < hgt s (G.ev i).1 := fun q hq => G.Rt_T hi hq hs
  have hV : (G.T i).filter (fun t => hgt s (G.m (i + 1)) < hgt t (G.m (i + 1))) =
      (G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i)) := by
    ext t
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (G.T_T hi hs h1).mpr h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (G.T_T hi hs h1).mp h2⟩
  have hVsub : (G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i)) ⊆ G.sp i :=
    fun t ht => (G.T_sp (Finset.mem_filter.mp ht).1).1
  have hVsub1 : (G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i)) ⊆ G.sp (i + 1) :=
    fun t ht => (G.T_sp (Finset.mem_filter.mp ht).1).2
  have hVtr : G.low (i + 1) ((G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i))) =
      G.low i ((G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i))) :=
    G.low_transfer hVsub1 (fun _ ha _ hb h =>
      (G.T_T hi (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1).mpr h)
  have hVconn : G.Conn (i, G.low i ((G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i))))
      (i + 1, G.low i ((G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i)))) :=
    G.conn_rel (G.node_low hi.le hVsub) (by rw [← hVtr]; exact G.node_low hi hVsub1)
      (G.rel_through hi (fun _ ht => (Finset.mem_filter.mp (G.low_some ht).1).1))
  -- a segment ending (starting) at the event is above `s` when `s` passes below the event
  have hLab : ¬ (G.ev i).2 < hgt s (G.ev i).1 → ∀ l ∈ G.Lf i, hgt s (G.m i) < hgt l (G.m i) := by
    intro hab l hl
    have h1 := G.mem_sp.mp (G.Lf_sp hi hl)
    exact lt_of_le_of_ne (not_lt.mp (fun h => hab ((hLs l hl).mp h)))
      (G.hgt_ne hsS h1.1 (G.Lf_ne_T hi hl hs).symm (G.mem_T.mp hs).2.1 h1.2)
  have hRab : ¬ (G.ev i).2 < hgt s (G.ev i).1 →
      ∀ q ∈ G.Rt i, hgt s (G.m (i + 1)) < hgt q (G.m (i + 1)) := by
    intro hab q hq
    have h1 := G.mem_sp.mp (G.Rt_sp hi hq)
    exact lt_of_le_of_ne (not_lt.mp (fun h => hab ((hRs q hq).mp h)))
      (G.hgt_ne hsS h1.1 (G.Rt_ne_T hi hq hs).symm (G.mem_T.mp hs).2.2 h1.2)
  by_cases hab : (G.ev i).2 < hgt s (G.ev i).1
  · -- `s` passes above the event point
    have e1 : G.succ i s = G.low i ((G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i))) := by
      unfold succ
      congr 1
      ext t
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        rcases G.sp_cases hi h1 with h | h
        · exact ⟨h, h2⟩
        · exact absurd h2 (not_lt.mpr ((hLs t h).mpr hab).le)
      · rintro ⟨h1, h2⟩
        exact ⟨(G.T_sp h1).1, h2⟩
    have e2 : G.succ (i + 1) s =
        G.low (i + 1) ((G.T i).filter (fun t => hgt s (G.m (i + 1)) < hgt t (G.m (i + 1)))) := by
      unfold succ
      congr 1
      ext t
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        rcases G.sp1_cases hi h1 with h | h
        · exact ⟨h, h2⟩
        · exact absurd h2 (not_lt.mpr ((hRs t h).mpr hab).le)
      · rintro ⟨h1, h2⟩
        exact ⟨(G.T_sp h1).2, h2⟩
    rw [e1, e2, hV, hVtr]
    exact hVconn
  · have hbe : hgt s (G.ev i).1 < (G.ev i).2 :=
      lt_of_le_of_ne (not_lt.mp hab) (G.T_ne_ev hi hs)
    by_cases hex : ∃ t ∈ G.T i, hgt t (G.ev i).1 < (G.ev i).2 ∧ hgt s (G.m i) < hgt t (G.m i)
    · obtain ⟨t, ht, htb, hst⟩ := hex
      have htL : ∀ l ∈ G.Lf i, hgt t (G.m i) < hgt l (G.m i) := by
        intro l hl
        have h1 := G.mem_sp.mp (G.Lf_sp hi hl)
        have h2 := G.mem_T.mp ht
        exact lt_of_le_of_ne (not_lt.mp (fun h => absurd ((G.Lf_T hi hl ht).mp h) (not_lt.mpr htb.le)))
          (G.hgt_ne h2.1 h1.1 (G.Lf_ne_T hi hl ht).symm h2.2.1 h1.2)
      have htR : ∀ q ∈ G.Rt i, hgt t (G.m (i + 1)) < hgt q (G.m (i + 1)) := by
        intro q hq
        have h1 := G.mem_sp.mp (G.Rt_sp hi hq)
        have h2 := G.mem_T.mp ht
        exact lt_of_le_of_ne (not_lt.mp (fun h => absurd ((G.Rt_T hi hq ht).mp h) (not_lt.mpr htb.le)))
          (G.hgt_ne h2.1 h1.1 (G.Rt_ne_T hi hq ht).symm h2.2.2 h1.2)
      have e1 : G.succ i s = G.low i ((G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i))) := by
        unfold succ
        have hU : (G.sp i).filter (fun t => hgt s (G.m i) < hgt t (G.m i)) =
            (G.T i).filter (fun t => hgt s (G.m i) < hgt t (G.m i)) ∪ G.Lf i := by
          ext u
          rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro ⟨h1, h2⟩
            rcases G.sp_cases hi h1 with h | h
            · exact Or.inl ⟨h, h2⟩
            · exact Or.inr h
          · rintro (⟨h1, h2⟩ | h)
            · exact ⟨(G.T_sp h1).1, h2⟩
            · exact ⟨G.Lf_sp hi h, hLab hab u h⟩
        rw [hU]
        exact G.low_union hVsub (Finset.mem_filter.mpr ⟨ht, hst⟩) htL
      have e2 : G.succ (i + 1) s =
          G.low (i + 1) ((G.T i).filter (fun t => hgt s (G.m (i + 1)) < hgt t (G.m (i + 1)))) := by
        unfold succ
        have hU : (G.sp (i + 1)).filter (fun t => hgt s (G.m (i + 1)) < hgt t (G.m (i + 1))) =
            (G.T i).filter (fun t => hgt s (G.m (i + 1)) < hgt t (G.m (i + 1))) ∪ G.Rt i := by
          ext u
          rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro ⟨h1, h2⟩
            rcases G.sp1_cases hi h1 with h | h
            · exact Or.inl ⟨h, h2⟩
            · exact Or.inr h
          · rintro (⟨h1, h2⟩ | h)
            · exact ⟨(G.T_sp h1).2, h2⟩
            · exact ⟨G.Rt_sp hi h, hRab hab u h⟩
        rw [hU]
        exact G.low_union (fun x hx => (G.T_sp (Finset.mem_filter.mp hx).1).2)
          (Finset.mem_filter.mpr ⟨ht, (G.T_T hi hs ht).mp hst⟩) htR
      rw [e1, e2, hV, hVtr]
      exact hVconn
    · simp only [not_exists, not_and, not_lt] at hex
      have e1 : G.succ i s = G.loL i := by
        rw [G.loL_eq hi]
        unfold succ
        congr 1
        ext u
        rw [Finset.mem_filter, Finset.mem_union, G.mem_Tab]
        constructor
        · rintro ⟨h1, h2⟩
          rcases G.sp_cases hi h1 with h | h
          · refine Or.inr ⟨h, ?_⟩
            by_contra hc
            have hub : hgt u (G.ev i).1 < (G.ev i).2 :=
              lt_of_le_of_ne (not_lt.mp hc) (G.T_ne_ev hi h)
            exact absurd h2 (not_lt.mpr (hex u h hub))
          · exact Or.inl h
        · rintro (h | ⟨h1, h2⟩)
          · exact ⟨G.Lf_sp hi h, hLab hab u h⟩
          · exact ⟨(G.T_sp h1).1, (G.T_T_L hi hs h1).mpr (by linarith)⟩
      have e2 : G.succ (i + 1) s = G.loR i := by
        rw [G.loR_eq hi]
        unfold succ
        congr 1
        ext u
        rw [Finset.mem_filter, Finset.mem_union, G.mem_Tab]
        constructor
        · rintro ⟨h1, h2⟩
          rcases G.sp1_cases hi h1 with h | h
          · refine Or.inr ⟨h, ?_⟩
            by_contra hc
            have hub : hgt u (G.ev i).1 < (G.ev i).2 :=
              lt_of_le_of_ne (not_lt.mp hc) (G.T_ne_ev hi h)
            exact absurd ((G.T_T hi hs h).mpr h2) (not_lt.mpr (hex u h hub))
          · exact Or.inl h
        · rintro (h | ⟨h1, h2⟩)
          · exact ⟨G.Rt_sp hi h, hRab hab u h⟩
          · exact ⟨(G.T_sp h1).2, (G.T_T_R hi hs h1).mp (by linarith)⟩
      rw [e1, e2]
      exact G.conn_rel (G.node_loL hi) (G.node_loR hi) (G.rel_bottom hi)

end SL

/-! ## M4c: segment darts, the component map, invariance under the face walk -/

namespace SL
variable (G : SL)

/-- Head of a segment dart (`true` = traversed left to right). -/
def hd (d : Sg × Bool) : Pt := if d.2 then d.1.2 else d.1.1
/-- Tail of a segment dart. -/
def tl (d : Sg × Bool) : Pt := if d.2 then d.1.1 else d.1.2

/-- The gap on the left of dart `d`, in strip `i`. -/
noncomputable def side (i : ℕ) (d : Sg × Bool) : ℕ × Option Sg :=
  if d.2 then (i, G.succ i d.1) else (i, some d.1)

theorem node_side {i : ℕ} (hi : i ≤ G.P.card) {d : Sg × Bool} (hs : d.1 ∈ G.sp i) :
    G.side i d ∈ G.nodes := by
  unfold side
  split_ifs
  · exact G.node_succ hi d.1
  · exact G.node_some hi hs

theorem side_conn {s : Sg} (hs : s ∈ G.S) (dir : Bool) :
    ∀ j, G.rk s.1 + 1 ≤ j → j ≤ G.rk s.2 →
      G.Conn (G.side (G.rk s.1 + 1) (s, dir)) (G.side j (s, dir)) := by
  have h2 := G.rk_lt_card (G.mem2 s hs)
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro hle
    exact G.conn_refl (G.node_side (by omega)
      (G.mem_sp.mpr ⟨hs, (G.spans_iff hs _).mpr ⟨by omega, hle⟩⟩))
  | succ n hn ih =>
    intro hle
    have hT : s ∈ G.T n := G.mem_T.mpr ⟨hs, (G.spans_iff hs _).mpr ⟨by omega, by omega⟩,
      (G.spans_iff hs _).mpr ⟨by omega, hle⟩⟩
    have hn' : n < G.P.card := by omega
    refine G.conn_trans (ih (by omega)) ?_
    cases dir
    · exact G.along_below hn' hT
    · exact G.along_above hn' hT

open Classical in
/-- A raw gap node as a vertex of `H` (junk default off the node set). -/
noncomputable def nd (a : ℕ × Option Sg) : {n // n ∈ G.nodes} :=
  if h : a ∈ G.nodes then ⟨a, h⟩
  else ⟨(0, none), G.mem_nodes.mpr ⟨Nat.zero_le _, fun _ h => by simp at h⟩⟩

/-- The face (component of `H`) on the left of a segment dart. -/
noncomputable def cc (d : Sg × Bool) : G.H.ConnectedComponent :=
  G.H.connectedComponentMk (G.nd (G.side (G.rk d.1.1 + 1) d))

theorem cc_eq_of_conn {a b : ℕ × Option Sg} (h : G.Conn a b) :
    G.H.connectedComponentMk (G.nd a) = G.H.connectedComponentMk (G.nd b) := by
  obtain ⟨ha, hb, h⟩ := h
  unfold nd
  rw [dif_pos ha, dif_pos hb]
  exact SimpleGraph.ConnectedComponent.sound h

open Classical in
/-- The face walk on segment darts: leave the head along the next segment clockwise. -/
noncomputable def nxt (d : Sg × Bool) : Sg × Bool :=
  (G.ncw (G.rk (hd d)) d.1, decide ((G.ncw (G.rk (hd d)) d.1).1 = hd d))

theorem inc_iff {w : Pt} (hw : w ∈ G.P) {u : Sg} :
    (u ∈ G.Rt (G.rk w) ∨ u ∈ G.Lf (G.rk w)) ↔ u ∈ G.S ∧ (u.1 = w ∨ u.2 = w) := by
  rw [G.mem_Rt, G.mem_Lf, G.ev_rk hw]
  tauto

theorem ncw_mem {r : ℕ} {s : Sg} (hs : s ∈ G.Rt r ∨ s ∈ G.Lf r) :
    G.ncw r s ∈ G.Rt r ∨ G.ncw r s ∈ G.Lf r := by
  unfold ncw
  split_ifs with h
  · rcases h1 : G.high (r + 1) (G.Rbelow r s) with _ | β
    · rcases h2 : G.low r (G.Lf r) with _ | β
      · rcases h3 : G.high (r + 1) (G.Rt r) with _ | β
        · rw [Option.getD_none, Option.getD_none, Option.getD_none]
          exact hs
        · rw [Option.getD_none, Option.getD_none, Option.getD_some]
          exact Or.inl (G.high_some h3).1
      · rw [Option.getD_none, Option.getD_some]
        exact Or.inr (G.low_some h2).1
    · rw [Option.getD_some]
      exact Or.inl (G.mem_Rbelow.mp (G.high_some h1).1).1
  · rcases h1 : G.low r (G.Labove r s) with _ | β
    · rcases h2 : G.high (r + 1) (G.Rt r) with _ | β
      · rcases h3 : G.low r (G.Lf r) with _ | β
        · rw [Option.getD_none, Option.getD_none, Option.getD_none]
          exact hs
        · rw [Option.getD_none, Option.getD_none, Option.getD_some]
          exact Or.inr (G.low_some h3).1
      · rw [Option.getD_none, Option.getD_some]
        exact Or.inl (G.high_some h2).1
    · rw [Option.getD_some]
      exact Or.inr (G.mem_Labove.mp (G.low_some h1).1).1

theorem ncw_ne {r : ℕ} (hr : r < G.P.card) {s s' : Sg} (hs : s ∈ G.Rt r ∨ s ∈ G.Lf r)
    (hs' : s' ∈ G.Rt r ∨ s' ∈ G.Lf r) (hne : s' ≠ s) : G.ncw r s ≠ s := by
  unfold ncw
  split_ifs with h
  · have hsR : s ∈ G.Rt r := by
      rcases hs with hs | hs
      · exact hs
      · exact absurd h (G.Lf_fst hs)
    rcases h1 : G.high (r + 1) (G.Rbelow r s) with _ | β
    · rcases h2 : G.low r (G.Lf r) with _ | β
      · obtain ⟨β, h3⟩ := G.high_isSome (i := r + 1) ⟨s, hsR⟩
        rw [Option.getD_none, Option.getD_none, h3, Option.getD_some]
        intro e
        subst e
        have hLe := G.low_none h2
        have hs'R : s' ∈ G.Rt r := by
          rcases hs' with hs' | hs'
          · exact hs'
          · rw [hLe] at hs'; exact absurd hs' (Finset.notMem_empty _)
        have hmax := (G.high_some h3).2 s' hs'R
        have hnb : ¬ hgt s' (G.m (r + 1)) < hgt β (G.m (r + 1)) := by
          intro hlt
          have := G.mem_Rbelow.mpr ⟨hs'R, hlt⟩
          rw [G.high_none h1] at this
          exact Finset.notMem_empty _ this
        have h1' := G.mem_sp.mp (G.Rt_sp hr hsR)
        have h2' := G.mem_sp.mp (G.Rt_sp hr hs'R)
        exact G.hgt_ne h2'.1 h1'.1 hne h2'.2 h1'.2 (le_antisymm hmax (not_lt.mp hnb))
      · rw [Option.getD_none, Option.getD_some]
        intro e
        subst e
        exact G.Lf_fst (G.low_some h2).1 h
    · rw [Option.getD_some]
      intro e
      subst e
      exact lt_irrefl _ (G.mem_Rbelow.mp (G.high_some h1).1).2
  · have hsL : s ∈ G.Lf r := by
      rcases hs with hs | hs
      · exact absurd (G.mem_Rt.mp hs).2 h
      · exact hs
    rcases h1 : G.low r (G.Labove r s) with _ | β
    · rcases h2 : G.high (r + 1) (G.Rt r) with _ | β
      · obtain ⟨β, h3⟩ := G.low_isSome (i := r) ⟨s, hsL⟩
        rw [Option.getD_none, Option.getD_none, h3, Option.getD_some]
        intro e
        subst e
        have hRe := G.high_none h2
        have hs'L : s' ∈ G.Lf r := by
          rcases hs' with hs' | hs'
          · rw [hRe] at hs'; exact absurd hs' (Finset.notMem_empty _)
          · exact hs'
        have hmin := (G.low_some h3).2 s' hs'L
        have hna : ¬ hgt β (G.m r) < hgt s' (G.m r) := by
          intro hlt
          have := G.mem_Labove.mpr ⟨hs'L, hlt⟩
          rw [G.low_none h1] at this
          exact Finset.notMem_empty _ this
        have h1' := G.mem_sp.mp (G.Lf_sp hr hsL)
        have h2' := G.mem_sp.mp (G.Lf_sp hr hs'L)
        exact G.hgt_ne h2'.1 h1'.1 hne h2'.2 h1'.2 (le_antisymm (not_lt.mp hna) hmin)
      · rw [Option.getD_none, Option.getD_some]
        intro e
        subst e
        exact G.Lf_fst hsL (G.mem_Rt.mp (G.high_some h2).1).2
    · rw [Option.getD_some]
      intro e
      subst e
      exact lt_irrefl _ (G.mem_Labove.mp (G.low_some h1).1).2

theorem hd_mem {d : Sg × Bool} (hdS : d.1 ∈ G.S) : hd d ∈ G.P := by
  unfold SL.hd
  split_ifs
  · exact G.mem2 _ hdS
  · exact G.mem1 _ hdS

theorem inc_hd {d : Sg × Bool} (hdS : d.1 ∈ G.S) :
    d.1 ∈ G.Rt (G.rk (SL.hd d)) ∨ d.1 ∈ G.Lf (G.rk (SL.hd d)) := by
  rw [G.inc_iff (G.hd_mem hdS)]
  refine ⟨hdS, ?_⟩
  unfold SL.hd
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem nxt_mem {d : Sg × Bool} (hdS : d.1 ∈ G.S) : (G.nxt d).1 ∈ G.S :=
  ((G.inc_iff (G.hd_mem hdS)).mp (G.ncw_mem (G.inc_hd hdS))).1

theorem nxt_inc {d : Sg × Bool} (hdS : d.1 ∈ G.S) :
    (G.nxt d).1.1 = SL.hd d ∨ (G.nxt d).1.2 = SL.hd d :=
  ((G.inc_iff (G.hd_mem hdS)).mp (G.ncw_mem (G.inc_hd hdS))).2

theorem tl_nxt {d : Sg × Bool} (hdS : d.1 ∈ G.S) : tl (G.nxt d) = SL.hd d := by
  classical
  have h := G.nxt_inc hdS
  unfold tl nxt
  simp only
  split_ifs with h1
  · exact of_decide_eq_true h1
  · have h2 : ¬ (G.ncw (G.rk (SL.hd d)) d.1).1 = SL.hd d := fun e => h1 (decide_eq_true e)
    unfold nxt at h
    rcases h with h | h
    · exact absurd h h2
    · exact h

/-- If `d.1` and `s'` are the only segments at the head of `d`, the walk turns onto `s'`. -/
theorem nxt_deg2 {d : Sg × Bool} (hdS : d.1 ∈ G.S) {s' : Sg} (hs' : s' ∈ G.S)
    (hs'i : s'.1 = SL.hd d ∨ s'.2 = SL.hd d) (hne : s' ≠ d.1)
    (honly : ∀ u ∈ G.S, (u.1 = SL.hd d ∨ u.2 = SL.hd d) → u = d.1 ∨ u = s') :
    (G.nxt d).1 = s' := by
  have hw := G.hd_mem hdS
  have hmem := (G.inc_iff hw).mp (G.ncw_mem (G.inc_hd hdS))
  rcases honly _ hmem.1 hmem.2 with h | h
  · exact absurd h (G.ncw_ne (G.rk_lt_card hw) (G.inc_hd hdS) ((G.inc_iff hw).mpr ⟨hs', hs'i⟩) hne)
  · exact h

/-- If the walk turns back onto the same segment, the head has degree one. -/
theorem nxt_fix {d : Sg × Bool} (hdS : d.1 ∈ G.S) (hfix : (G.nxt d).1 = d.1) :
    ∀ u ∈ G.S, (u.1 = SL.hd d ∨ u.2 = SL.hd d) → u = d.1 := by
  intro u hu hui
  by_contra hne
  have hw := G.hd_mem hdS
  exact G.ncw_ne (G.rk_lt_card hw) (G.inc_hd hdS) ((G.inc_iff hw).mpr ⟨hu, hui⟩) hne hfix

/-- The face on the left is invariant under the face walk. -/
theorem cc_nxt {d : Sg × Bool} (hdS : d.1 ∈ G.S) : G.cc (G.nxt d) = G.cc d := by
  classical
  obtain ⟨s, dir⟩ := d
  have hs : s ∈ G.S := hdS
  have hw := G.hd_mem (d := (s, dir)) hdS
  set w := SL.hd (s, dir) with hwdef
  set r := G.rk w with hrdef
  have hr : r < G.P.card := G.rk_lt_card hw
  have hev : G.ev r = w := G.ev_rk hw
  have hinc := G.inc_hd (d := (s, dir)) hdS
  have hwed := G.wedge hr hinc
  set β := G.ncw r s with hβ
  have hβm := G.ncw_mem hinc
  have hβS : β ∈ G.S := by rcases hβm with h | h <;> [exact (G.mem_Rt.mp h).1; exact (G.mem_Lf.mp h).1]
  -- the arriving side is connected to the dart's first-strip side
  have hA : G.Conn (G.side (G.rk s.1 + 1) (s, dir)) (G.arr r s) := by
    cases dir
    · have hs1 : s.1 = w := by rw [hwdef]; unfold SL.hd; simp
      have harr : G.arr r s = (G.rk s.1 + 1, some s) := by
        unfold arr
        rw [if_neg (fun e => G.Rt_snd (G.mem_Rt.mpr ⟨hs, hs1.trans hev.symm⟩) e), hs1]
      rw [harr]
      unfold side
      simp only [Bool.false_eq_true, if_false]
      exact G.conn_refl (G.node_some (by rw [hs1]; exact hr)
        (G.mem_sp.mpr ⟨hs, (G.spans_iff hs _).mpr ⟨by omega, by
          have := G.rk_seg hs; omega⟩⟩))
    · have hs2 : s.2 = w := by rw [hwdef]; unfold SL.hd; simp
      have harr : G.arr r s = (G.rk s.2, G.succ (G.rk s.2) s) := by
        unfold arr
        rw [if_pos (hs2.trans hev.symm), hs2]
      rw [harr]
      have := G.side_conn hs true (G.rk s.2) (G.rk_seg hs) le_rfl
      unfold side at this
      simpa using this
  -- the leaving side is connected to the next dart's first-strip side
  have hB : G.Conn (G.lv r β) (G.side (G.rk (G.nxt (s, dir)).1.1 + 1) (G.nxt (s, dir))) := by
    have hn1 : (G.nxt (s, dir)).1 = β := rfl
    have hn2 : (G.nxt (s, dir)).2 = decide (β.1 = w) := rfl
    by_cases hb1 : β.1 = w
    · have hlv : G.lv r β = (r + 1, G.succ (r + 1) β) := by
        unfold lv; rw [if_pos (hb1.trans hev.symm)]
      rw [hlv]
      unfold side
      rw [hn2, hn1, decide_eq_true hb1]
      simp only [if_true]
      rw [hb1]
      exact G.conn_refl (G.node_succ hr β)
    · have hb2 : β.2 = w := by
        rcases G.nxt_inc hdS with h | h
        · exact absurd h hb1
        · exact h
      have hlv : G.lv r β = (r, some β) := by
        unfold lv; rw [if_neg (fun e => hb1 (e.trans hev))]
      rw [hlv]
      unfold side
      rw [hn2, hn1, decide_eq_false hb1]
      simp only [Bool.false_eq_true, if_false]
      have := G.side_conn hβS false (G.rk β.2) (G.rk_seg hβS) le_rfl
      unfold side at this
      simp only [Bool.false_eq_true, if_false] at this
      rw [hb2] at this
      exact G.conn_symm this
  have := G.cc_eq_of_conn (G.conn_trans hA (G.conn_trans hwed hB))
  unfold cc
  exact this.symm

theorem conn_none {a b : ℕ} (ha : a ≤ G.P.card) (hb : b ≤ G.P.card) :
    G.Conn (a, none) (b, none) := by
  have h0 : ∀ c, c ≤ G.P.card → G.Conn (0, none) (c, none) := by
    intro c
    induction c with
    | zero => intro h; exact G.conn_refl (G.mem_nodes.mpr ⟨h, fun _ h => by simp at h⟩)
    | succ n ih =>
      intro h
      exact G.conn_trans (ih (by omega))
        (G.conn_rel (G.mem_nodes.mpr ⟨by omega, fun _ h => by simp at h⟩)
          (G.mem_nodes.mpr ⟨h, fun _ h => by simp at h⟩)
          (G.rel_through (by omega) (fun _ h => by simp at h)))
  exact G.conn_trans (G.conn_symm (h0 a ha)) (h0 b hb)

/-- Every face is on the left of some segment dart. -/
theorem cc_surj (hS : G.S.Nonempty) (n : {n // n ∈ G.nodes}) :
    ∃ d : Sg × Bool, d.1 ∈ G.S ∧ G.cc d = G.H.connectedComponentMk n := by
  classical
  obtain ⟨⟨i, g⟩, hn⟩ := n
  have hn' := G.mem_nodes.mp hn
  have hnd : ∀ h : (i, g) ∈ G.nodes, G.nd (i, g) = ⟨(i, g), h⟩ := fun h => by
    unfold nd; rw [dif_pos h]
  cases g with
  | some s =>
    have hs := G.mem_sp.mp (hn'.2 s rfl)
    have hk := (G.spans_iff hs.1 i).mp hs.2
    refine ⟨(s, false), hs.1, ?_⟩
    have := G.cc_eq_of_conn (G.side_conn hs.1 false i (by omega) hk.2)
    unfold cc
    rw [this]
    unfold side
    simp only [Bool.false_eq_true, if_false]
    rw [hnd hn]
  | none =>
    obtain ⟨s0, hs0⟩ := hS
    have hk0 := G.rk_seg hs0
    have hK0 := G.rk_lt_card (G.mem2 s0 hs0)
    set j := G.rk s0.1 + 1 with hj
    have hjsp : s0 ∈ G.sp j := G.mem_sp.mpr ⟨hs0, (G.spans_iff hs0 j).mpr ⟨by omega, by omega⟩⟩
    obtain ⟨t, ht⟩ := G.high_isSome (i := j) ⟨s0, hjsp⟩
    obtain ⟨htsp, htmax⟩ := G.high_some ht
    have htS := G.mem_sp.mp htsp
    have htk := (G.spans_iff htS.1 j).mp htS.2
    have hsucc : G.succ j t = none := by
      unfold succ
      convert G.low_empty j
      ext u
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
      exact fun hu => htmax u hu
    refine ⟨(t, true), htS.1, ?_⟩
    have h1 := G.side_conn htS.1 true j (by omega) htk.2
    unfold side at h1
    simp only [if_true] at h1
    rw [hsucc] at h1
    have h2 := G.conn_trans h1 (G.conn_none (a := j) (b := i) (by omega) hn'.1)
    have := G.cc_eq_of_conn h2
    unfold cc side
    simp only [if_true]
    rw [this, hnd hn]

end SL


/-! ## M5: chains, the chain face walk, and the polygonal edge bound -/

/-- The segment with endpoints `a`, `b`, oriented left to right. -/
noncomputable def orient (a b : Pt) : Sg := if a.1 < b.1 then (a, b) else (b, a)

/-- The segment dart from `x.1` to `x.2`. -/
noncomputable def toD (x : Pt × Pt) : Sg × Bool :=
  if x.1.1 < x.2.1 then ((x.1, x.2), true) else ((x.2, x.1), false)

theorem toD_fst (x : Pt × Pt) : (toD x).1 = orient x.1 x.2 := by
  unfold toD orient
  by_cases h : x.1.1 < x.2.1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem hd_toD (x : Pt × Pt) : SL.hd (toD x) = x.2 := by
  unfold toD SL.hd
  by_cases h : x.1.1 < x.2.1
  · rw [if_pos h]; rfl
  · rw [if_neg h]; rfl

theorem orient_comm {a b : Pt} (h : a.1 ≠ b.1) : orient a b = orient b a := by
  unfold orient
  by_cases h1 : a.1 < b.1
  · rw [if_pos h1, if_neg (not_lt.mpr h1.le)]
  · rw [if_neg h1, if_pos (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h))]

theorem orient_eq {a b a' b' : Pt} (h : orient a b = orient a' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  unfold orient at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> tauto

theorem orient_ne {a b : Pt} (h : (orient a b).1.1 < (orient a b).2.1) : a.1 ≠ b.1 := by
  intro e
  unfold orient at h
  rw [if_neg (by rw [e]; exact lt_irrefl _)] at h
  simp only at h
  rw [e] at h
  exact lt_irrefl _ h

theorem orient_inc_l (a b : Pt) : (orient a b).1 = a ∨ (orient a b).2 = a := by
  unfold orient
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem orient_inc_r (a b : Pt) : (orient a b).1 = b ∨ (orient a b).2 = b := by
  unfold orient
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem fst_eq_orient {d : Sg × Bool} (h : d.1.1.1 < d.1.2.1) :
    d.1 = orient (SL.tl d) (SL.hd d) := by
  obtain ⟨⟨p, q⟩, b⟩ := d
  cases b
  · unfold SL.tl SL.hd orient
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg (not_lt.mpr (le_of_lt h))]
  · unfold SL.tl SL.hd orient
    simp only [if_true]
    rw [if_pos h]

theorem toD_pair {d : Sg × Bool} (h : d.1.1.1 < d.1.2.1) : toD (SL.tl d, SL.hd d) = d := by
  obtain ⟨⟨p, q⟩, b⟩ := d
  cases b
  · unfold SL.tl SL.hd toD
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg (not_lt.mpr (le_of_lt h))]
  · unfold SL.tl SL.hd toD
    simp only [if_true]
    rw [if_pos h]

namespace SL
variable (G : SL)

/-- The face walk on point-pair darts. -/
noncomputable def nxtP (x : Pt × Pt) : Pt × Pt := (tl (G.nxt (toD x)), hd (G.nxt (toD x)))

/-- The face on the left of a point-pair dart. -/
noncomputable def ccP (x : Pt × Pt) : G.H.ConnectedComponent := G.cc (toD x)

theorem ccP_nxtP {x : Pt × Pt} (hx : orient x.1 x.2 ∈ G.S) : G.ccP (G.nxtP x) = G.ccP x := by
  have hx' : (toD x).1 ∈ G.S := by rw [toD_fst]; exact hx
  unfold ccP nxtP
  rw [toD_pair (G.hor _ (G.nxt_mem hx')), G.cc_nxt hx']

theorem nxtP_fst {x : Pt × Pt} (hx : orient x.1 x.2 ∈ G.S) : (G.nxtP x).1 = x.2 := by
  have hx' : (toD x).1 ∈ G.S := by rw [toD_fst]; exact hx
  unfold nxtP
  rw [G.tl_nxt hx', hd_toD]

theorem nxtP_orient {x : Pt × Pt} (hx : orient x.1 x.2 ∈ G.S) :
    orient (G.nxtP x).1 (G.nxtP x).2 = (G.nxt (toD x)).1 := by
  have hx' : (toD x).1 ∈ G.S := by rw [toD_fst]; exact hx
  unfold nxtP
  exact (fst_eq_orient (G.hor _ (G.nxt_mem hx'))).symm

theorem nxtP_mem {x : Pt × Pt} (hx : orient x.1 x.2 ∈ G.S) :
    orient (G.nxtP x).1 (G.nxtP x).2 ∈ G.S := by
  rw [G.nxtP_orient hx]
  exact G.nxt_mem (by rw [toD_fst]; exact hx)

theorem nxtP_deg2 {a c e : Pt} (hac : orient a c ∈ G.S) (hce : orient c e ∈ G.S) (hne : e ≠ a)
    (honly : ∀ u ∈ G.S, (u.1 = c ∨ u.2 = c) → u = orient a c ∨ u = orient c e) :
    G.nxtP (a, c) = (c, e) := by
  have hx' : (toD (a, c)).1 ∈ G.S := by rw [toD_fst]; exact hac
  have hhd : SL.hd (toD (a, c)) = c := hd_toD _
  have hne' : orient c e ≠ (toD (a, c)).1 := by
    rw [toD_fst]
    intro h
    rcases orient_eq h with ⟨h1, h2⟩ | ⟨_, h2⟩
    · exact hne (h2.trans h1)
    · exact hne h2
  have hi : (orient c e).1 = SL.hd (toD (a, c)) ∨ (orient c e).2 = SL.hd (toD (a, c)) := by
    rw [hhd]; exact orient_inc_l c e
  have h1 := G.nxt_deg2 hx' hce hi hne' (by
    intro u hu hui
    rw [hhd] at hui
    rw [toD_fst]
    exact honly u hu hui)
  have htl := G.nxtP_fst (x := (a, c)) hac
  have hor := G.nxtP_orient (x := (a, c)) hac
  rw [h1, htl] at hor
  rcases orient_eq hor with ⟨_, h2⟩ | ⟨h2, _⟩
  · exact Prod.ext htl h2
  · exfalso
    have := G.hor _ hce
    rw [← h2] at this
    unfold orient at this
    rw [if_neg (lt_irrefl _)] at this
    exact lt_irrefl _ this

theorem nxtP_fix {a c : Pt} (hac : orient a c ∈ G.S) (hfix : G.nxtP (a, c) = (c, a)) :
    ∀ u ∈ G.S, (u.1 = c ∨ u.2 = c) → u = orient a c := by
  have hx' : (toD (a, c)).1 ∈ G.S := by rw [toD_fst]; exact hac
  have hor := G.nxtP_orient (x := (a, c)) hac
  rw [hfix] at hor
  have hfix' : (G.nxt (toD (a, c))).1 = (toD (a, c)).1 := by
    rw [← hor, toD_fst]
    exact orient_comm (Ne.symm (orient_ne (G.hor _ hac)))
  intro u hu hui
  have := G.nxt_fix hx' hfix' u hu (by rw [hd_toD]; exact hui)
  rw [this, toD_fst]

theorem ccP_surj (hS : G.S.Nonempty) (n : {n // n ∈ G.nodes}) :
    ∃ x : Pt × Pt, orient x.1 x.2 ∈ G.S ∧ G.ccP x = G.H.connectedComponentMk n := by
  obtain ⟨d, hd, h⟩ := G.cc_surj hS n
  refine ⟨(SL.tl d, SL.hd d), ?_, ?_⟩
  · rw [← fst_eq_orient (G.hor _ hd)]; exact hd
  · unfold ccP; rw [toD_pair (G.hor _ hd)]; exact h

end SL

/-- A polygonal plane drawing on top of a straight-line drawing `G`: chains `pt i 0, …,
pt i (n i - 1)` whose ends are real vertices `Vp` and whose inner points are bends of degree 2. -/
structure PLS (ι : Type*) where
  G : SL
  Vp : Finset Pt
  n : ι → ℕ
  pt : ι → ℕ → Pt
  len : ∀ i, 2 ≤ n i
  nodup : ∀ i k l, k < n i → l < n i → pt i k = pt i l → k = l
  end0 : ∀ i, pt i 0 ∈ Vp
  end1 : ∀ i, pt i (n i - 1) ∈ Vp
  inner : ∀ i k, 0 < k → k + 1 < n i → pt i k ∉ Vp
  segS : ∀ i k, k + 1 < n i → orient (pt i k) (pt i (k + 1)) ∈ G.S
  deg2 : ∀ i k, 0 < k → k + 1 < n i → ∀ s ∈ G.S, (s.1 = pt i k ∨ s.2 = pt i k) →
    s = orient (pt i (k - 1)) (pt i k) ∨ s = orient (pt i k) (pt i (k + 1))
  cover : ∀ s ∈ G.S, ∃ i k, k + 1 < n i ∧ s = orient (pt i k) (pt i (k + 1))
  segInj : ∀ i j k l, k + 1 < n i → l + 1 < n j →
    orient (pt i k) (pt i (k + 1)) = orient (pt j l) (pt j (l + 1)) → i = j ∧ k = l
  ptsCover : ∀ p ∈ G.P, p ∈ Vp ∨ ∃ i k, 0 < k ∧ k + 1 < n i ∧ p = pt i k
  noPar : ∀ i j, i ≠ j → ¬ ((pt i 0 = pt j 0 ∧ pt i (n i - 1) = pt j (n j - 1)) ∨
    (pt i 0 = pt j (n j - 1) ∧ pt i (n i - 1) = pt j 0))
  noK2 : ∀ i, ∃ j, j ≠ i ∧ (pt j 0 = pt i 0 ∨ pt j (n j - 1) = pt i 0 ∨
    pt j 0 = pt i (n i - 1) ∨ pt j (n j - 1) = pt i (n i - 1))

namespace PLS
variable {ι : Type*} (X : PLS ι)

theorem xne {i : ι} {k : ℕ} (hk : k + 1 < X.n i) : (X.pt i k).1 ≠ (X.pt i (k + 1)).1 :=
  orient_ne (X.G.hor _ (X.segS i k hk))

theorem segS' {i : ι} {k : ℕ} (hk : k + 1 < X.n i) :
    orient (X.pt i (k + 1)) (X.pt i k) ∈ X.G.S := by
  rw [orient_comm (Ne.symm (X.xne hk))]
  exact X.segS i k hk

theorem fwd (i : ι) : ∀ k, k + 1 < X.n i →
    X.G.ccP (X.pt i k, X.pt i (k + 1)) = X.G.ccP (X.pt i 0, X.pt i 1) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [← ih (by omega)]
    have h := X.G.nxtP_deg2 (a := X.pt i k) (c := X.pt i (k + 1)) (e := X.pt i (k + 1 + 1))
      (X.segS i k (by omega)) (X.segS i (k + 1) hk)
      (fun e => by have := X.nodup i (k + 1 + 1) k (by omega) (by omega) e; omega)
      (by
        intro u hu hui
        have := X.deg2 i (k + 1) (by omega) hk u hu hui
        simpa using this)
    rw [← h]
    exact X.G.ccP_nxtP (X.segS i k (by omega))

theorem bwd (i : ι) : ∀ j k, k + 1 < X.n i → X.n i - 2 - k = j →
    X.G.ccP (X.pt i (k + 1), X.pt i k) = X.G.ccP (X.pt i (X.n i - 1), X.pt i (X.n i - 2)) := by
  intro j
  induction j with
  | zero =>
    intro k hk hj
    rw [show k + 1 = X.n i - 1 by omega, show k = X.n i - 2 by omega]
  | succ j ih =>
    intro k hk hj
    rw [← ih (k + 1) (by omega) (by omega)]
    have hk1 : k + 1 + 1 < X.n i := by omega
    have h := X.G.nxtP_deg2 (a := X.pt i (k + 1 + 1)) (c := X.pt i (k + 1)) (e := X.pt i k)
      (X.segS' hk1) (X.segS' hk)
      (fun e => by have := X.nodup i k (k + 1 + 1) (by omega) (by omega) e; omega)
      (by
        intro u hu hui
        have := X.deg2 i (k + 1) (by omega) hk1 u hu hui
        simp only [Nat.add_sub_cancel] at this
        rcases this with h | h
        · right; rw [h]; exact orient_comm (X.xne hk)
        · left; rw [h]; exact orient_comm (X.xne hk1))
    rw [← h]
    exact X.G.ccP_nxtP (X.segS' hk1)

/-- First and last segment darts of a chain dart `(i, forward?)`. -/
def fsd (D : ι × Bool) : Pt × Pt :=
  if D.2 then (X.pt D.1 0, X.pt D.1 1) else (X.pt D.1 (X.n D.1 - 1), X.pt D.1 (X.n D.1 - 2))

def lsd (D : ι × Bool) : Pt × Pt :=
  if D.2 then (X.pt D.1 (X.n D.1 - 2), X.pt D.1 (X.n D.1 - 1)) else (X.pt D.1 1, X.pt D.1 0)

/-- The face on the left of a chain dart. -/
noncomputable def comp (D : ι × Bool) : X.G.H.ConnectedComponent := X.G.ccP (X.fsd D)

theorem last_eq (i : ι) : X.n i - 2 + 1 = X.n i - 1 := by have := X.len i; omega

theorem lastS (i : ι) : orient (X.pt i (X.n i - 2)) (X.pt i (X.n i - 1)) ∈ X.G.S := by
  have h := X.segS i (X.n i - 2) (by have := X.len i; omega)
  rwa [X.last_eq i] at h

theorem lastS' (i : ι) : orient (X.pt i (X.n i - 1)) (X.pt i (X.n i - 2)) ∈ X.G.S := by
  have h := X.segS' (i := i) (k := X.n i - 2) (by have := X.len i; omega)
  rwa [X.last_eq i] at h

theorem lsd_mem (D : ι × Bool) : orient (X.lsd D).1 (X.lsd D).2 ∈ X.G.S := by
  unfold lsd
  split_ifs
  · exact X.lastS D.1
  · exact X.segS' (k := 0) (by have := X.len D.1; omega)

theorem comp_lsd (D : ι × Bool) : X.G.ccP (X.lsd D) = X.comp D := by
  unfold comp lsd fsd
  split_ifs
  · have h := X.fwd D.1 (X.n D.1 - 2) (by have := X.len D.1; omega)
    rwa [X.last_eq] at h
  · have h := X.bwd D.1 (X.n D.1 - 2) 0 (by have := X.len D.1; omega) (by omega)
    simpa using h

theorem exists_next (D : ι × Bool) : ∃ E, X.fsd E = X.G.nxtP (X.lsd D) := by
  have hm := X.G.nxtP_mem (X.lsd_mem D)
  have hf := X.G.nxtP_fst (X.lsd_mem D)
  have hv : (X.lsd D).2 ∈ X.Vp := by
    unfold lsd
    split_ifs
    · exact X.end1 D.1
    · exact X.end0 D.1
  obtain ⟨j, k, hk, he⟩ := X.cover _ hm
  rcases orient_eq he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hk0 : k = 0 := by
      by_contra hne
      exact X.inner j k (by omega) hk (by rw [← h1, hf]; exact hv)
    subst hk0
    refine ⟨(j, true), ?_⟩
    unfold fsd
    simp only [if_true]
    exact Prod.ext h1.symm h2.symm
  · have hk1 : k + 2 = X.n j := by
      by_contra hne
      exact X.inner j (k + 1) (by omega) (by omega) (by rw [← h1, hf]; exact hv)
    refine ⟨(j, false), ?_⟩
    unfold fsd
    simp only [Bool.false_eq_true, if_false]
    rw [show X.n j - 1 = k + 1 by omega, show X.n j - 2 = k by omega]
    exact Prod.ext h1.symm h2.symm

/-- The chain face walk. -/
noncomputable def Φ (D : ι × Bool) : ι × Bool := Classical.choose (X.exists_next D)

theorem fsd_Φ (D : ι × Bool) : X.fsd (X.Φ D) = X.G.nxtP (X.lsd D) :=
  Classical.choose_spec (X.exists_next D)

theorem comp_Φ (D : ι × Bool) : X.comp (X.Φ D) = X.comp D := by
  unfold comp
  rw [X.fsd_Φ, X.G.ccP_nxtP (X.lsd_mem D), X.comp_lsd]
  rfl

theorem tail_Φ (D : ι × Bool) : (X.fsd (X.Φ D)).1 = (X.lsd D).2 := by
  rw [X.fsd_Φ]
  exact X.G.nxtP_fst (X.lsd_mem D)

theorem ends_ne (i : ι) : X.pt i 0 ≠ X.pt i (X.n i - 1) := by
  intro e
  have := X.nodup i 0 (X.n i - 1) (by have := X.len i; omega) (by have := X.len i; omega) e
  have := X.len i
  omega

theorem Φ_ne (D : ι × Bool) : X.Φ D ≠ D := by
  intro e
  have h := X.tail_Φ D
  rw [e] at h
  unfold fsd lsd at h
  split_ifs at h
  · exact X.ends_ne D.1 h
  · exact X.ends_ne D.1 h.symm

/-- Degree-one end: the walk turns back at the head of a chain end segment. -/
theorem deg1_of_turn {i : ι} {a v : Pt} (hav : orient a v ∈ X.G.S) (hturn : X.G.nxtP (a, v) = (v, a))
    (hseg : orient a v = orient (X.pt i 0) (X.pt i 1) ∨
      orient a v = orient (X.pt i (X.n i - 2)) (X.pt i (X.n i - 1)))
    {j : ι} {b c : Pt} (hbc : orient b c = orient (X.pt j 0) (X.pt j 1) ∨
      orient b c = orient (X.pt j (X.n j - 2)) (X.pt j (X.n j - 1)))
    (hbcS : orient b c ∈ X.G.S) (hinc : b = v) : j = i := by
  have h := X.G.nxtP_fix hav hturn (orient b c) hbcS (by rw [← hinc]; exact orient_inc_l b c)
  have hl := X.len i
  have hl' := X.len j
  have key : ∀ k l, k + 1 < X.n j → l + 1 < X.n i →
      orient b c = orient (X.pt j k) (X.pt j (k + 1)) →
      orient a v = orient (X.pt i l) (X.pt i (l + 1)) → j = i := by
    intro k l hk hl2 e1 e2
    exact (X.segInj j i k l hk hl2 (e1.symm.trans (h.trans e2))).1
  rcases hbc with e1 | e1 <;> rcases hseg with e2 | e2
  · exact key 0 0 (by omega) (by omega) e1 e2
  · exact key 0 (X.n i - 2) (by omega) (by omega) e1 (by rw [X.last_eq]; exact e2)
  · exact key (X.n j - 2) 0 (by omega) (by omega) (by rw [X.last_eq]; exact e1) e2
  · exact key (X.n j - 2) (X.n i - 2) (by omega) (by omega) (by rw [X.last_eq]; exact e1)
      (by rw [X.last_eq]; exact e2)

theorem Φ_Φ_ne (D : ι × Bool) : X.Φ (X.Φ D) ≠ D := by
  intro hDD
  set E := X.Φ D with hE
  have h1 := X.tail_Φ D
  have h2 := X.tail_Φ E
  rw [hDD] at h2
  obtain ⟨i, b⟩ := D
  obtain ⟨j, b'⟩ := E
  have hl := X.len i
  have hl' := X.len j
  by_cases hij : j = i
  · subst hij
    have hb : b' = !b := by
      cases b <;> cases b'
      · exact absurd (by rw [← hE] : X.Φ (j, false) = (j, false)) (X.Φ_ne _)
      · rfl
      · rfl
      · exact absurd (by rw [← hE] : X.Φ (j, true) = (j, true)) (X.Φ_ne _)
    subst hb
    have hf1 := X.fsd_Φ (j, b)
    have hf2 := X.fsd_Φ (j, !b)
    rw [← hE] at hf1
    rw [hDD] at hf2
    obtain ⟨k, hk, hkend⟩ := X.noK2 j
    -- both ends of chain j have degree one
    have t0 : X.G.nxtP (X.pt j 1, X.pt j 0) = (X.pt j 0, X.pt j 1) := by
      cases b
      · unfold fsd lsd at hf1; simpa using hf1.symm
      · unfold fsd lsd at hf2; simpa using hf2.symm
    have t1 : X.G.nxtP (X.pt j (X.n j - 2), X.pt j (X.n j - 1)) =
        (X.pt j (X.n j - 1), X.pt j (X.n j - 2)) := by
      cases b
      · unfold fsd lsd at hf2; simpa using hf2.symm
      · unfold fsd lsd at hf1; simpa using hf1.symm
    have s0 : orient (X.pt j 1) (X.pt j 0) = orient (X.pt j 0) (X.pt j 1) :=
      orient_comm (Ne.symm (X.xne (k := 0) (by omega)))
    have hk2 := X.len k
    have nk : (X.pt k (X.n k - 1)).1 ≠ (X.pt k (X.n k - 2)).1 := by
      have := X.xne (i := k) (k := X.n k - 2) (by omega)
      rw [X.last_eq] at this
      exact Ne.symm this
    have sk : orient (X.pt k (X.n k - 1)) (X.pt k (X.n k - 2)) =
        orient (X.pt k (X.n k - 2)) (X.pt k (X.n k - 1)) := orient_comm nk
    have hj0 := X.segS' (i := j) (k := 0) (by omega)
    have hk0 := X.segS k 0 (by omega)
    rcases hkend with e | e | e | e
    · exact hk (X.deg1_of_turn hj0 t0 (Or.inl s0) (Or.inl rfl) hk0 e)
    · exact hk (X.deg1_of_turn hj0 t0 (Or.inl s0) (Or.inr sk) (X.lastS' k) e)
    · exact hk (X.deg1_of_turn (X.lastS j) t1 (Or.inr rfl) (Or.inl rfl) hk0 e)
    · exact hk (X.deg1_of_turn (X.lastS j) t1 (Or.inr rfl) (Or.inr sk) (X.lastS' k) e)
  · rw [← hE] at h1
    apply X.noPar i j (Ne.symm hij)
    unfold fsd lsd at h1 h2
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, if_false, if_true] at h1 h2 <;>
      first
        | exact Or.inl ⟨h1.symm, h2⟩
        | exact Or.inr ⟨h1.symm, h2⟩
        | exact Or.inl ⟨h2, h1.symm⟩
        | exact Or.inr ⟨h2, h1.symm⟩

theorem comp_of_seg {x : Pt × Pt} (hx : orient x.1 x.2 ∈ X.G.S) :
    ∃ D, X.comp D = X.G.ccP x := by
  obtain ⟨i, k, hk, he⟩ := X.cover _ hx
  rcases orient_eq he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(i, true), ?_⟩
    unfold comp fsd
    simp only [if_true]
    rw [← X.fwd i k hk, show x = (x.1, x.2) from rfl, h1, h2]
  · refine ⟨(i, false), ?_⟩
    unfold comp fsd
    simp only [Bool.false_eq_true, if_false]
    rw [← X.bwd i _ k hk rfl, show x = (x.1, x.2) from rfl, h1, h2]

theorem three_comp [Fintype ι] [Nonempty ι] :
    3 * Nat.card X.G.H.ConnectedComponent ≤ 2 * Fintype.card ι := by
  classical
  have i0 : ι := Classical.arbitrary ι
  have hS : X.G.S.Nonempty := ⟨_, X.segS i0 0 (by have := X.len i0; omega)⟩
  rw [Nat.card_eq_fintype_card]
  have h := Finset.mul_card_image_le_card_of_maps_to (s := (Finset.univ : Finset (ι × Bool)))
    (t := (Finset.univ : Finset X.G.H.ConnectedComponent)) (f := X.comp)
    (fun _ _ => Finset.mem_univ _) 3 (by
      intro c _
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h v =>
        obtain ⟨x, hx, hcx⟩ := X.G.ccP_surj hS v
        obtain ⟨D, hD⟩ := X.comp_of_seg hx
        have hc : X.comp D = X.G.H.connectedComponentMk v := hD.trans hcx
        have hsub : ({D, X.Φ D, X.Φ (X.Φ D)} : Finset (ι × Bool)) ⊆
            Finset.univ.filter (fun D' => X.comp D' = X.G.H.connectedComponentMk v) := by
          intro D' hD'
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hD'
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rcases hD' with rfl | rfl | rfl
          · exact hc
          · rw [X.comp_Φ]; exact hc
          · rw [X.comp_Φ, X.comp_Φ]; exact hc
        have hcard : ({D, X.Φ D, X.Φ (X.Φ D)} : Finset (ι × Bool)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair (X.Φ_ne (X.Φ D)).symm]
          rw [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨(X.Φ_ne D).symm, (X.Φ_Φ_ne D).symm⟩
        rw [← hcard]
        exact Finset.card_le_card hsub)
  rw [Finset.card_univ, Finset.card_univ, Fintype.card_prod, Fintype.card_bool] at h
  linarith

theorem card_S [Fintype ι] : X.G.S.card = ∑ i, (X.n i - 1) := by
  classical
  have hS : X.G.S = (Finset.univ.sigma (fun i => Finset.range (X.n i - 1))).image
      (fun p => orient (X.pt p.1 p.2) (X.pt p.1 (p.2 + 1))) := by
    ext s
    rw [Finset.mem_image]
    constructor
    · intro hs
      obtain ⟨i, k, hk, he⟩ := X.cover s hs
      exact ⟨⟨i, k⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (show k < X.n i - 1 by omega)⟩, he.symm⟩
    · rintro ⟨⟨i, k⟩, hp, rfl⟩
      have h := (Finset.mem_sigma.mp hp).2
      rw [Finset.mem_range] at h
      dsimp only at h ⊢
      exact X.segS i k (by omega)
  rw [hS, Finset.card_image_of_injOn, Finset.card_sigma]
  · simp only [Finset.card_range]
  · rintro ⟨i, k⟩ hp ⟨j, l⟩ hq he
    have hk := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    have hl := Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    dsimp only at hk hl he
    obtain ⟨rfl, rfl⟩ := X.segInj i j k l (by omega) (by omega) he
    rfl

theorem card_P [Fintype ι] : X.G.P.card ≤ X.Vp.card + ∑ i, (X.n i - 2) := by
  classical
  have hsub : X.G.P ⊆ X.Vp ∪ (Finset.univ.sigma (fun i => Finset.range (X.n i - 2))).image
      (fun p => X.pt p.1 (p.2 + 1)) := by
    intro p hp
    rw [Finset.mem_union, Finset.mem_image]
    rcases X.ptsCover p hp with h | ⟨i, k, hk0, hk, rfl⟩
    · exact Or.inl h
    · refine Or.inr ⟨⟨i, k - 1⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (show k - 1 < X.n i - 2 by omega)⟩, ?_⟩
      simp only
      rw [Nat.sub_add_cancel hk0]
  calc X.G.P.card ≤ _ := Finset.card_le_card hsub
    _ ≤ X.Vp.card + _ := Finset.card_union_le _ _
    _ ≤ X.Vp.card + ∑ i, (X.n i - 2) := by
      have := Finset.card_image_le (s := Finset.univ.sigma (fun i => Finset.range (X.n i - 2)))
        (f := fun p => X.pt p.1 (p.2 + 1))
      rw [Finset.card_sigma] at this
      simp only [Finset.card_range] at this
      omega

/-- The polygonal edge bound: a PL plane drawing with no K2 component has `|E| ≤ 3|V| - 3`. -/
theorem edge_bound [Fintype ι] [Nonempty ι] : 3 + Fintype.card ι ≤ 3 * X.Vp.card := by
  have h1 := X.G.comp_lower
  have h2 := X.three_comp
  have h3 := X.card_S
  have h4 := X.card_P
  have h5 : ∑ i, (X.n i - 1) = ∑ i, (X.n i - 2) + Fintype.card ι := by
    rw [← Finset.card_univ, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have := X.len i
    omega
  omega

end PLS


/-! ## M6: shear the polygonal drawing into distinct abscissae, build the `SL`/`PLS` -/

theorem onSeg_iff {A B q : Pt} (h : A.1 < B.1) : onSeg (A, B) q ↔ q ∈ segment ℝ A B := by
  have hd : 0 < B.1 - A.1 := by linarith
  rw [segment_eq_image ℝ A B]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(q.1 - A.1) / (B.1 - A.1), ⟨div_nonneg (by linarith) hd.le,
      (div_le_one hd).mpr (by linarith)⟩, ?_⟩
    obtain ⟨q1, q2⟩ := q
    simp only at h1 h2 h3
    rw [h3]
    unfold hgt slope
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      ring
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    simp only [onSeg, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    unfold hgt slope
    field_simp
    ring

theorem onSeg_orient {a b q : Pt} (h : a.1 ≠ b.1) : onSeg (orient a b) q ↔ q ∈ segment ℝ a b := by
  unfold orient
  by_cases h1 : a.1 < b.1
  · rw [if_pos h1]
    exact onSeg_iff h1
  · rw [if_neg h1, onSeg_iff (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h)), segment_symm]

theorem orient_fst_mem (a b : Pt) : (orient a b).1 = a ∨ (orient a b).1 = b := by
  unfold orient; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem orient_snd_mem (a b : Pt) : (orient a b).2 = a ∨ (orient a b).2 = b := by
  unfold orient; split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The plane of the drawing. -/
abbrev E2 := Fin 2 → ℝ

/-- The shear `p ↦ (p 0 + c p 1, p 1)`. -/
noncomputable def shear (c : ℝ) : E2 →ₗ[ℝ] ℝ × ℝ where
  toFun p := (p 0 + c * p 1, p 1)
  map_add' p q := by
    simp only [Pi.add_apply, Prod.mk_add_mk]
    congr 1
    ring
  map_smul' a p := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_mk]
    congr 1
    ring

theorem shear_apply (c : ℝ) (p : E2) : shear c p = (p 0 + c * p 1, p 1) := rfl

theorem shear_inj (c : ℝ) : Function.Injective (shear c) := by
  intro p q h
  rw [shear_apply, shear_apply, Prod.mk.injEq] at h
  funext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [h.2] at h
    linarith [h.1]
  · exact h.2

theorem shear_segment (c : ℝ) (a b : E2) :
    shear c '' segment ℝ a b = segment ℝ (shear c a) (shear c b) := by
  have := image_segment ℝ (shear c).toAffineMap a b
  rwa [LinearMap.coe_toAffineMap] at this

theorem exists_shear (Q : Finset E2) :
    ∃ c : ℝ, ∀ p ∈ Q, ∀ q ∈ Q, (shear c p).1 = (shear c q).1 → p = q := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    ((Q ×ˢ Q).image (fun pq : E2 × E2 => (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1)))
  refine ⟨c, fun p hp q hq h => ?_⟩
  rw [shear_apply, shear_apply] at h
  simp only at h
  by_cases h1 : p 1 = q 1
  · have h0 : p 0 = q 0 := by rw [h1] at h; linarith
    funext k
    fin_cases k
    · exact h0
    · exact h1
  · exfalso
    apply hc
    rw [Finset.mem_image]
    refine ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    have hne : p 1 - q 1 ≠ 0 := sub_ne_zero.mpr h1
    simp only
    field_simp
    linarith

/-- A polygonal plane drawing in `Fin 2 → ℝ` (output of the approximation step). -/
structure PLD (ι : Type*) where
  Vp : Finset E2
  n : ι → ℕ
  pt : ι → ℕ → E2
  len : ∀ i, 2 ≤ n i
  nodup : ∀ i k l, k < n i → l < n i → pt i k = pt i l → k = l
  end0 : ∀ i, pt i 0 ∈ Vp
  end1 : ∀ i, pt i (n i - 1) ∈ Vp
  inner : ∀ i k, 0 < k → k + 1 < n i → pt i k ∉ Vp
  bend : ∀ i j k l, i ≠ j → 0 < k → k + 1 < n i → l < n j → pt i k ≠ pt j l
  simple : ∀ i k l, k + 1 < l → l + 1 < n i → ∀ q, q ∈ segment ℝ (pt i k) (pt i (k + 1)) →
    q ∉ segment ℝ (pt i l) (pt i (l + 1))
  consec : ∀ i k, k + 2 < n i → ∀ q, q ∈ segment ℝ (pt i k) (pt i (k + 1)) →
    q ∈ segment ℝ (pt i (k + 1)) (pt i (k + 2)) → q = pt i (k + 1)
  cross : ∀ i j k l, i ≠ j → k + 1 < n i → l + 1 < n j → ∀ q,
    q ∈ segment ℝ (pt i k) (pt i (k + 1)) → q ∈ segment ℝ (pt j l) (pt j (l + 1)) → q ∈ Vp
  vavoid : ∀ i k, k + 1 < n i → ∀ v ∈ Vp, v ∈ segment ℝ (pt i k) (pt i (k + 1)) →
    v = pt i k ∨ v = pt i (k + 1)
  noPar : ∀ i j, i ≠ j → ¬ ((pt i 0 = pt j 0 ∧ pt i (n i - 1) = pt j (n j - 1)) ∨
    (pt i 0 = pt j (n j - 1) ∧ pt i (n i - 1) = pt j 0))
  noK2 : ∀ i, ∃ j, j ≠ i ∧ (pt j 0 = pt i 0 ∨ pt j (n j - 1) = pt i 0 ∨
    pt j 0 = pt i (n i - 1) ∨ pt j (n j - 1) = pt i (n i - 1))

namespace PLD
variable {ι : Type*} [Fintype ι] (X : PLD ι)

open Classical in
/-- All points of the drawing. -/
noncomputable def Q : Finset E2 :=
  X.Vp ∪ Finset.univ.biUnion (fun i => (Finset.range (X.n i)).image (X.pt i))

theorem pt_mem_Q {i : ι} {k : ℕ} (hk : k < X.n i) : X.pt i k ∈ X.Q := by
  classical
  unfold Q
  rw [Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩⟩

theorem Vp_sub_Q : X.Vp ⊆ X.Q := by
  classical
  intro v hv
  unfold Q
  exact Finset.mem_union_left _ hv

theorem Q_cases {q : E2} (hq : q ∈ X.Q) :
    q ∈ X.Vp ∨ ∃ j l, 0 < l ∧ l + 1 < X.n j ∧ q = X.pt j l := by
  classical
  unfold Q at hq
  rw [Finset.mem_union, Finset.mem_biUnion] at hq
  rcases hq with h | ⟨j, _, h⟩
  · exact Or.inl h
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_range] at hl
    by_cases h0 : l = 0
    · subst h0; exact Or.inl (X.end0 j)
    · by_cases h1 : l + 1 = X.n j
      · left
        rw [show l = X.n j - 1 by omega]
        exact X.end1 j
      · exact Or.inr ⟨j, l, by omega, by omega, rfl⟩

/-- A point of the drawing lying on a segment of chain `i` is an endpoint of it. -/
theorem Q_on_seg {i : ι} {k : ℕ} (hk : k + 1 < X.n i) {q : E2} (hq : q ∈ X.Q)
    (hs : q ∈ segment ℝ (X.pt i k) (X.pt i (k + 1))) : q = X.pt i k ∨ q = X.pt i (k + 1) := by
  rcases X.Q_cases hq with h | ⟨j, l, hl0, hl, rfl⟩
  · exact X.vavoid i k hk q h hs
  · by_cases hij : j = i
    · subst hij
      have hl' := left_mem_segment ℝ (X.pt j l) (X.pt j (l + 1))
      rcases lt_trichotomy l k with h | h | h
      · by_cases h2 : l + 1 = k
        · subst h2
          have := X.consec j l (by omega) _ hl' hs
          exact absurd (X.nodup j l (l + 1) (by omega) (by omega) this) (by omega)
        · exact absurd hs (X.simple j l k (by omega) hk _ hl')
      · exact Or.inl (by rw [h])
      · by_cases h2 : l = k + 1
        · exact Or.inr (by rw [h2])
        · exact absurd hl' (X.simple j k l (by omega) hl _ hs)
    · have := X.cross i j k l (Ne.symm hij) hk hl _ hs (left_mem_segment ℝ _ _)
      exact absurd this (X.inner j l hl0 hl)

theorem seg_inter {i j : ι} {k l : ℕ} (hk : k + 1 < X.n i) (hl : l + 1 < X.n j)
    (hne : ¬ (i = j ∧ k = l)) {q : E2} (h1 : q ∈ segment ℝ (X.pt i k) (X.pt i (k + 1)))
    (h2 : q ∈ segment ℝ (X.pt j l) (X.pt j (l + 1))) : q ∈ X.Q := by
  by_cases hij : i = j
  · subst hij
    rcases lt_trichotomy k l with h | h | h
    · by_cases h3 : l = k + 1
      · subst h3
        rw [X.consec i k (by omega) q h1 h2]
        exact X.pt_mem_Q hk
      · exact absurd h2 (X.simple i k l (by omega) hl q h1)
    · exact absurd ⟨rfl, h⟩ hne
    · by_cases h3 : k = l + 1
      · subst h3
        rw [X.consec i l (by omega) q h2 h1]
        exact X.pt_mem_Q hl
      · exact absurd h1 (X.simple i l k (by omega) hk q h2)
  · exact X.Vp_sub_Q (X.cross i j k l hij hk hl q h1 h2)

variable (c : ℝ)

/-- Sheared chain points. -/
noncomputable def spt (i : ι) (k : ℕ) : Pt := shear c (X.pt i k)

open Classical in
noncomputable def sSL (hc : ∀ p ∈ X.Q, ∀ q ∈ X.Q, (shear c p).1 = (shear c q).1 → p = q) : SL where
  P := X.Q.image (shear c)
  S := (Finset.univ.sigma (fun i => Finset.range (X.n i - 1))).image
    (fun p => orient (X.spt c p.1 p.2) (X.spt c p.1 (p.2 + 1)))
  hor := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨⟨i, k⟩, hp, rfl⟩ := hs
    have hk := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    dsimp only at hk ⊢
    have hne : (X.spt c i k).1 ≠ (X.spt c i (k + 1)).1 := by
      intro e
      have := X.nodup i k (k + 1) (by omega) (by omega)
        (hc _ (X.pt_mem_Q (by omega)) _ (X.pt_mem_Q (by omega)) e)
      omega
    unfold orient
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
  mem1 := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨⟨i, k⟩, hp, rfl⟩ := hs
    have hk := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    dsimp only at hk ⊢
    rcases orient_fst_mem (X.spt c i k) (X.spt c i (k + 1)) with h | h <;> rw [h] <;>
      exact Finset.mem_image_of_mem _ (X.pt_mem_Q (by omega))
  mem2 := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨⟨i, k⟩, hp, rfl⟩ := hs
    have hk := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    dsimp only at hk ⊢
    rcases orient_snd_mem (X.spt c i k) (X.spt c i (k + 1)) with h | h <;> rw [h] <;>
      exact Finset.mem_image_of_mem _ (X.pt_mem_Q (by omega))
  xinj := by
    intro p hp q hq h
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    rw [hc p' hp' q' hq' h]
  disj := by
    intro s hs t ht hst q h1 h2
    obtain ⟨⟨i, k⟩, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨⟨j, l⟩, hp2, rfl⟩ := Finset.mem_image.mp ht
    have hk := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    have hl := Finset.mem_range.mp (Finset.mem_sigma.mp hp2).2
    dsimp only at hk hl h1 h2 hst
    have hx : ∀ {i : ι} {k : ℕ}, k + 1 < X.n i → (X.spt c i k).1 ≠ (X.spt c i (k + 1)).1 := by
      intro i k hk e
      have := X.nodup i k (k + 1) (by omega) (by omega)
        (hc _ (X.pt_mem_Q (by omega)) _ (X.pt_mem_Q (by omega)) e)
      omega
    rw [onSeg_orient (hx (by omega)), spt, spt, ← shear_segment] at h1 h2
    obtain ⟨q1, hq1, rfl⟩ := h1
    obtain ⟨q2, hq2, e⟩ := h2
    have e' := shear_inj c e
    subst e'
    refine Finset.mem_image_of_mem _ (X.seg_inter (by omega) (by omega) ?_ hq1 hq2)
    rintro ⟨rfl, rfl⟩
    exact hst rfl
  avoid := by
    intro s hs q hq h1
    obtain ⟨⟨i, k⟩, hp, rfl⟩ := Finset.mem_image.mp hs
    have hk := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    dsimp only at hk h1 ⊢
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    have hx : (X.spt c i k).1 ≠ (X.spt c i (k + 1)).1 := by
      intro e
      have := X.nodup i k (k + 1) (by omega) (by omega)
        (hc _ (X.pt_mem_Q (by omega)) _ (X.pt_mem_Q (by omega)) e)
      omega
    rw [onSeg_orient hx, spt, spt, ← shear_segment] at h1
    obtain ⟨q1, hq1, e⟩ := h1
    have e' := shear_inj c e
    subst e'
    have hend := X.Q_on_seg (by omega) hq' hq1
    unfold orient
    split_ifs
    · rcases hend with h | h
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; rfl)
    · rcases hend with h | h
      · exact Or.inr (by rw [h]; rfl)
      · exact Or.inl (by rw [h]; rfl)

end PLD

namespace PLD
variable {ι : Type*} [Fintype ι] (X : PLD ι)

theorem exists_c : ∃ c : ℝ, ∀ p ∈ X.Q, ∀ q ∈ X.Q, (shear c p).1 = (shear c q).1 → p = q :=
  exists_shear X.Q

/-- A shear making all abscissae distinct. -/
noncomputable def c0 : ℝ := Classical.choose X.exists_c

theorem c0_spec : ∀ p ∈ X.Q, ∀ q ∈ X.Q, (shear X.c0 p).1 = (shear X.c0 q).1 → p = q :=
  Classical.choose_spec X.exists_c

theorem mem_S {s : Sg} : s ∈ (X.sSL X.c0 X.c0_spec).S ↔
    ∃ i k, k + 1 < X.n i ∧ s = orient (X.spt X.c0 i k) (X.spt X.c0 i (k + 1)) := by
  classical
  show s ∈ (Finset.univ.sigma (fun i => Finset.range (X.n i - 1))).image _ ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨i, k⟩, hp, rfl⟩
    have hk := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    exact ⟨i, k, by dsimp only at hk; omega, rfl⟩
  · rintro ⟨i, k, hk, rfl⟩
    exact ⟨⟨i, k⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
      Finset.mem_range.mpr (show k < X.n i - 1 by omega)⟩, rfl⟩

theorem mem_P {p : Pt} : p ∈ (X.sSL X.c0 X.c0_spec).P ↔ ∃ q ∈ X.Q, shear X.c0 q = p := by
  classical
  show p ∈ X.Q.image _ ↔ _
  rw [Finset.mem_image]

open Classical in
/-- The sheared polygonal drawing as a `PLS`. -/
noncomputable def toPLS : PLS ι where
  G := X.sSL X.c0 X.c0_spec
  Vp := X.Vp.image (shear X.c0)
  n := X.n
  pt := X.spt X.c0
  len := X.len
  nodup := fun i k l hk hl e => X.nodup i k l hk hl (shear_inj _ e)
  end0 := fun i => Finset.mem_image_of_mem _ (X.end0 i)
  end1 := fun i => Finset.mem_image_of_mem _ (X.end1 i)
  inner := by
    intro i k h0 h1 h
    obtain ⟨v, hv, e⟩ := Finset.mem_image.mp h
    exact X.inner i k h0 h1 (by rw [← shear_inj _ e]; exact hv)
  segS := fun i k hk => (X.mem_S).mpr ⟨i, k, hk, rfl⟩
  deg2 := by
    intro i k h0 h1 s hs hinc
    obtain ⟨j, l, hl, rfl⟩ := (X.mem_S).mp hs
    have hpt : X.pt i k = X.pt j l ∨ X.pt i k = X.pt j (l + 1) := by
      rcases hinc with h | h
      · rcases orient_fst_mem (X.spt X.c0 j l) (X.spt X.c0 j (l + 1)) with h' | h' <;>
          rw [h'] at h
        · exact Or.inl (shear_inj _ h).symm
        · exact Or.inr (shear_inj _ h).symm
      · rcases orient_snd_mem (X.spt X.c0 j l) (X.spt X.c0 j (l + 1)) with h' | h' <;>
          rw [h'] at h
        · exact Or.inl (shear_inj _ h).symm
        · exact Or.inr (shear_inj _ h).symm
    by_cases hij : i = j
    · subst hij
      rcases hpt with h | h
      · have := X.nodup i k l (by omega) (by omega) h
        subst this
        exact Or.inr rfl
      · have := X.nodup i k (l + 1) (by omega) (by omega) h
        subst this
        exact Or.inl (by rw [Nat.add_sub_cancel])
    · exfalso
      rcases hpt with h | h
      · exact X.bend i j k l hij h0 h1 (by omega) h
      · exact X.bend i j k (l + 1) hij h0 h1 hl h
  cover := fun s hs => (X.mem_S).mp hs
  segInj := by
    intro i j k l hk hl e
    have key : (X.pt i k = X.pt j l ∧ X.pt i (k + 1) = X.pt j (l + 1)) ∨
        (X.pt i k = X.pt j (l + 1) ∧ X.pt i (k + 1) = X.pt j l) := by
      rcases orient_eq e with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨shear_inj _ h1, shear_inj _ h2⟩
      · exact Or.inr ⟨shear_inj _ h1, shear_inj _ h2⟩
    by_cases hij : i = j
    · subst hij
      rcases key with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact ⟨rfl, X.nodup i k l (by omega) (by omega) h1⟩
      · have := X.nodup i k (l + 1) (by omega) (by omega) h1
        have := X.nodup i (k + 1) l (by omega) (by omega) h2
        omega
    · exfalso
      have bi : ∀ m, 0 < m → m + 1 < X.n i → ∀ m', m' < X.n j → X.pt i m ≠ X.pt j m' :=
        fun m h0 h1 m' h2 => X.bend i j m m' hij h0 h1 h2
      have bj : ∀ m, 0 < m → m + 1 < X.n j → ∀ m', m' < X.n i → X.pt j m ≠ X.pt i m' :=
        fun m h0 h1 m' h2 => X.bend j i m m' (Ne.symm hij) h0 h1 h2
      rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hk0 : k = 0 := by
          by_contra h; exact bi k (by omega) hk l (by omega) h1
        have hk1 : k + 2 = X.n i := by
          by_contra h; exact bi (k + 1) (by omega) (by omega) (l + 1) hl h2
        have hl0 : l = 0 := by
          by_contra h; exact bj l (by omega) hl k (by omega) h1.symm
        have hl1 : l + 2 = X.n j := by
          by_contra h; exact bj (l + 1) (by omega) (by omega) (k + 1) hk h2.symm
        subst hk0 hl0
        apply X.noPar i j hij
        left
        rw [show X.n i - 1 = 0 + 1 by omega, show X.n j - 1 = 0 + 1 by omega]
        exact ⟨h1, h2⟩
      · have hk0 : k = 0 := by
          by_contra h; exact bi k (by omega) hk (l + 1) hl h1
        have hk1 : k + 2 = X.n i := by
          by_contra h; exact bi (k + 1) (by omega) (by omega) l (by omega) h2
        have hl0 : l = 0 := by
          by_contra h; exact bj l (by omega) hl (k + 1) hk h2.symm
        have hl1 : l + 2 = X.n j := by
          by_contra h; exact bj (l + 1) (by omega) (by omega) k (by omega) h1.symm
        subst hk0 hl0
        apply X.noPar i j hij
        right
        rw [show X.n i - 1 = 0 + 1 by omega, show X.n j - 1 = 0 + 1 by omega]
        exact ⟨h1, h2⟩
  ptsCover := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := (X.mem_P).mp hp
    rcases X.Q_cases hq with h | ⟨j, l, h0, h1, rfl⟩
    · exact Or.inl (Finset.mem_image_of_mem _ h)
    · exact Or.inr ⟨j, l, h0, h1, rfl⟩
  noPar := by
    intro i j hij h
    apply X.noPar i j hij
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨shear_inj _ h1, shear_inj _ h2⟩
    · exact Or.inr ⟨shear_inj _ h1, shear_inj _ h2⟩
  noK2 := by
    intro i
    obtain ⟨j, hj, h⟩ := X.noK2 i
    refine ⟨j, hj, ?_⟩
    unfold spt
    rcases h with h | h | h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h])))

/-- The polygonal edge bound in the original plane. -/
theorem edge_bound [Nonempty ι] : 3 + Fintype.card ι ≤ 3 * X.Vp.card := by
  classical
  have h := X.toPLS.edge_bound
  have hc : X.toPLS.Vp.card = X.Vp.card := Finset.card_image_of_injective _ (shear_inj _)
  rw [hc] at h
  exact h

end PLD


/-! ## M7: loop erasure of polygonal chains -/

/-- `y 0, …, y (n-1)` is a simple polyline. -/
structure SChain (n : ℕ) (y : ℕ → E2) : Prop where
  len : 2 ≤ n
  nodup : ∀ k l, k < n → l < n → y k = y l → k = l
  simple : ∀ k l, k + 1 < l → l + 1 < n → ∀ q, q ∈ segment ℝ (y k) (y (k + 1)) →
    q ∉ segment ℝ (y l) (y (l + 1))
  consec : ∀ k, k + 2 < n → ∀ q, q ∈ segment ℝ (y k) (y (k + 1)) →
    q ∈ segment ℝ (y (k + 1)) (y (k + 2)) → q = y (k + 1)

/-- Union of the segments of a polyline with `n` points. -/
def pimg (n : ℕ) (y : ℕ → E2) : Set E2 := {q | ∃ k, k + 1 < n ∧ q ∈ segment ℝ (y k) (y (k + 1))}

theorem pt_mem_pimg {n : ℕ} {y : ℕ → E2} (hn : 2 ≤ n) {k : ℕ} (hk : k < n) : y k ∈ pimg n y := by
  by_cases h : k + 1 < n
  · exact ⟨k, h, left_mem_segment ℝ _ _⟩
  · refine ⟨k - 1, by omega, ?_⟩
    rw [show k - 1 + 1 = k by omega]
    exact right_mem_segment ℝ _ _

theorem seg_closed (a b : E2) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))).isClosed

theorem seg_sub {a b c d : E2} (hc : c ∈ segment ℝ a b) (hd : d ∈ segment ℝ a b) :
    segment ℝ c d ⊆ segment ℝ a b :=
  (convex_segment a b).segment_subset hc hd

/-- On a segment meeting a closed set, the meeting point furthest toward `b`. -/
theorem far_point {a b : E2} {C : Set E2} (hC : IsClosed C) (hne : ∃ q ∈ segment ℝ a b, q ∈ C) :
    ∃ z ∈ segment ℝ a b, z ∈ C ∧ ∀ q ∈ segment ℝ z b, q ∈ C → q = z := by
  let f : ℝ → E2 := fun t => a + t • (b - a)
  have hfc : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hTc : IsCompact (Set.Icc (0 : ℝ) 1 ∩ f ⁻¹' C) := isCompact_Icc.inter_right (hC.preimage hfc)
  obtain ⟨q0, hq0, hq0C⟩ := hne
  rw [segment_eq_image', Set.mem_image] at hq0
  obtain ⟨t0, ht0, rfl⟩ := hq0
  obtain ⟨t, ⟨htI, htC⟩, htmax⟩ := hTc.exists_isGreatest ⟨t0, ht0, hq0C⟩
  refine ⟨f t, ?_, htC, ?_⟩
  · rw [segment_eq_image', Set.mem_image]
    exact ⟨t, htI, rfl⟩
  · intro q hq hqC
    rw [segment_eq_image', Set.mem_image] at hq
    obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hq
    have key : f t + s • (b - f t) = f (t + s * (1 - t)) := by
      funext i
      simp only [f, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [key] at hqC ⊢
    have h1 : 0 ≤ s * (1 - t) := mul_nonneg hs0 (by linarith [htI.2])
    have h2 : s * (1 - t) ≤ 1 - t := mul_le_of_le_one_left (by linarith [htI.2]) hs1
    have hle := htmax ⟨⟨by linarith [htI.1], by linarith⟩, hqC⟩
    have h3 : s * (1 - t) = 0 := le_antisymm (by linarith) h1
    rw [h3, add_zero]

theorem two_chain {a b : E2} (h : a ≠ b) : SChain 2 (fun k => if k = 0 then a else b) where
  len := le_rfl
  nodup := by
    intro k l hk hl e
    interval_cases k <;> interval_cases l
    · rfl
    · exact absurd e h
    · exact absurd e.symm h
    · rfl
  simple := by intro k l h1 h2; omega
  consec := by intro k h; omega

/-- Prepend a point to a simple polyline whose image meets the new segment only at its start. -/
theorem prepend {n : ℕ} {y : ℕ → E2} (hy : SChain n y) {p : E2} (hp : p ≠ y 0)
    (hmeet : ∀ q ∈ segment ℝ p (y 0), q ∈ pimg n y → q = y 0) :
    SChain (n + 1) (fun k => if k = 0 then p else y (k - 1)) where
  len := by have := hy.len; omega
  nodup := by
    have hpn : ∀ l, l < n → p ≠ y l := by
      intro l hl e
      exact hp (hmeet p (left_mem_segment ℝ _ _) (e ▸ pt_mem_pimg hy.len hl))
    intro k l hk hl e
    rcases Nat.eq_zero_or_pos k with rfl | hk0 <;> rcases Nat.eq_zero_or_pos l with rfl | hl0
    · rfl
    · simp only [if_neg (Nat.pos_iff_ne_zero.mp hl0)] at e
      exact absurd e (hpn (l - 1) (by omega))
    · simp only [if_neg (Nat.pos_iff_ne_zero.mp hk0)] at e
      exact absurd e.symm (hpn (k - 1) (by omega))
    · simp only [if_neg (Nat.pos_iff_ne_zero.mp hk0), if_neg (Nat.pos_iff_ne_zero.mp hl0)] at e
      have := hy.nodup (k - 1) (l - 1) (by omega) (by omega) e
      omega
  simple := by
    intro k l hkl hl q hq1 hq2
    simp only [show l ≠ 0 by omega, if_false, show l + 1 ≠ 0 by omega,
      show l + 1 - 1 = l - 1 + 1 by omega] at hq2
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [zero_add, if_neg one_ne_zero, Nat.sub_self] at hq1
      have hz := hmeet q hq1 ⟨l - 1, by omega, hq2⟩
      subst hz
      by_cases hl2 : l - 1 = 1
      · rw [hl2] at hq2
        have := hy.consec 0 (by omega) _ (left_mem_segment ℝ _ _) hq2
        exact absurd (hy.nodup 0 1 (by omega) (by omega) this) (by omega)
      · exact hy.simple 0 (l - 1) (by omega) (by omega) _ (left_mem_segment ℝ _ _) hq2
    · simp only [if_neg (Nat.pos_iff_ne_zero.mp hk0), show k + 1 ≠ 0 by omega, if_false,
        show k + 1 - 1 = k - 1 + 1 by omega] at hq1
      exact hy.simple (k - 1) (l - 1) (by omega) (by omega) q hq1 hq2
  consec := by
    intro k hk q hq1 hq2
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [zero_add, if_neg one_ne_zero, Nat.sub_self,
        show (2 : ℕ) ≠ 0 by omega, if_false] at hq1 hq2 ⊢
      exact hmeet q hq1 ⟨0, by omega, hq2⟩
    · simp only [if_neg (Nat.pos_iff_ne_zero.mp hk0), show k + 1 ≠ 0 by omega,
        show k + 2 ≠ 0 by omega, if_false, show k + 1 - 1 = k - 1 + 1 by omega,
        show k + 2 - 1 = k - 1 + 2 by omega] at hq1 hq2 ⊢
      exact hy.consec (k - 1) (by omega) q hq1 hq2

/-- Loop erasure: a polyline between distinct points contains a simple one. -/
theorem loop_erase : ∀ m (x : ℕ → E2), 1 ≤ m → x 0 ≠ x m →
    ∃ n y, SChain n y ∧ y 0 = x 0 ∧ y (n - 1) = x m ∧ pimg n y ⊆ pimg (m + 1) x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x hm hne
  classical
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨2, fun k => if k = 0 then x 0 else x 1, two_chain hne, rfl, rfl, ?_⟩
    rintro q ⟨k, hk, hq⟩
    refine ⟨0, by omega, ?_⟩
    obtain rfl : k = 0 := by omega
    simpa using hq
  have hS0 : IsClosed (segment ℝ (x 0) (x 1)) := seg_closed _ _
  let A := (Finset.range m).filter
    (fun j => ∃ q ∈ segment ℝ (x j) (x (j + 1)), q ∈ segment ℝ (x 0) (x 1))
  have h1A : 1 ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    x 1, left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
  let J := A.max' ⟨1, h1A⟩
  have hJA : J ∈ A := A.max'_mem _
  have hJm : J < m := Finset.mem_range.mp (Finset.mem_filter.mp hJA).1
  have hJ1 : 1 ≤ J := A.le_max' 1 h1A
  have hJmax : ∀ j, J < j → j < m → ∀ q ∈ segment ℝ (x j) (x (j + 1)),
      q ∉ segment ℝ (x 0) (x 1) := by
    intro j hj hjm q hq hq0
    have : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjm, q, hq, hq0⟩
    have := A.le_max' j this
    omega
  obtain ⟨z, hzJ, hz0, hzfar⟩ := far_point hS0 (Finset.mem_filter.mp hJA).2
  have hsub0 : segment ℝ (x 0) (x 1) ⊆ pimg (m + 1) x := fun q hq => ⟨0, by omega, hq⟩
  by_cases hzm : z = x m
  · refine ⟨2, fun k => if k = 0 then x 0 else x m, two_chain hne, rfl, rfl, ?_⟩
    rintro q ⟨k, hk, hq⟩
    obtain rfl : k = 0 := by omega
    simp only [zero_add, if_neg one_ne_zero] at hq
    exact hsub0 (seg_sub (left_mem_segment ℝ _ _) (hzm ▸ hz0) hq)
  -- recurse on z, x (J+1), …, x m
  let x' : ℕ → E2 := fun k => if k = 0 then z else x (J + k)
  have hx'm : x' (m - J) = x m := by
    simp only [x', show m - J ≠ 0 by omega, if_false, show J + (m - J) = m by omega]
  obtain ⟨n', y', hS', hy0', hyl', himg'⟩ := ih (m - J) (by omega) x' (by omega)
    (by rw [hx'm]; simpa [x'] using hzm)
  have hy0z : y' 0 = z := by rw [hy0']; simp [x']
  have hB : ∀ q ∈ pimg n' y', q ∈ segment ℝ (x 0) (x 1) → q = z := by
    intro q hq hq0
    obtain ⟨k, hk, hqk⟩ := himg' hq
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [x', if_pos rfl, zero_add, if_neg one_ne_zero] at hqk
      exact hzfar q hqk hq0
    · simp only [x', if_neg (Nat.pos_iff_ne_zero.mp hk0), show k + 1 ≠ 0 by omega, if_false,
        show J + (k + 1) = J + k + 1 by omega] at hqk
      exact absurd hq0 (hJmax (J + k) (by omega) (by omega) q hqk)
  have hC : pimg n' y' ⊆ pimg (m + 1) x := by
    intro q hq
    obtain ⟨k, hk, hqk⟩ := himg' hq
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [x', if_pos rfl, zero_add, if_neg one_ne_zero] at hqk
      exact ⟨J, by omega, seg_sub hzJ (right_mem_segment ℝ _ _) hqk⟩
    · simp only [x', if_neg (Nat.pos_iff_ne_zero.mp hk0), show k + 1 ≠ 0 by omega, if_false,
        show J + (k + 1) = J + k + 1 by omega] at hqk
      exact ⟨J + k, by omega, hqk⟩
  by_cases hz0' : z = x 0
  · exact ⟨n', y', hS', by rw [hy0z, hz0'], by rw [hyl', hx'm], hC⟩
  · refine ⟨n' + 1, fun k => if k = 0 then x 0 else y' (k - 1),
      prepend hS' (by rw [hy0z]; exact Ne.symm hz0') ?_, rfl, ?_, ?_⟩
    · intro q hq hqi
      rw [hy0z] at hq ⊢
      exact hB q hqi (seg_sub (left_mem_segment ℝ _ _) hz0 hq)
    · have := hS'.len
      simp only [show n' + 1 - 1 ≠ 0 by omega, if_false, show n' + 1 - 1 - 1 = n' - 1 by omega]
      rw [hyl', hx'm]
    · rintro q ⟨k, hk, hqk⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [zero_add, if_neg one_ne_zero, Nat.sub_self, hy0z] at hqk
        exact hsub0 (seg_sub (left_mem_segment ℝ _ _) hz0 hqk)
      · simp only [if_neg (Nat.pos_iff_ne_zero.mp hk0), show k + 1 ≠ 0 by omega, if_false,
          show k + 1 - 1 = k - 1 + 1 by omega] at hqk
        exact hC ⟨k - 1, by omega, hqk⟩


/-! ## M8a: raw polylines inside separated tubes give the edge bound -/

/-- If every edge has a raw polyline from `u i` to `v i` inside a set `Z i`, the sets `Z i` meet only in
real vertices, and `Z i` contains no real vertex other than `u i`, `v i`, then `|E| ≤ 3|V| - 3`
(for a nonempty edge set with distinct endpoint pairs and no isolated edge). -/
theorem edge_bound_of_tubes {ι : Type*} [Fintype ι] [Nonempty ι] (Vp : Finset E2) (u v : ι → E2)
    (huv : ∀ i, u i ≠ v i) (hu : ∀ i, u i ∈ Vp) (hv : ∀ i, v i ∈ Vp)
    (Z : ι → Set E2) (hZ : ∀ i j, i ≠ j → ∀ q, q ∈ Z i → q ∈ Z j → q ∈ Vp)
    (hZV : ∀ i, ∀ w ∈ Vp, w ∈ Z i → w = u i ∨ w = v i)
    (m : ι → ℕ) (x : ι → ℕ → E2) (hm : ∀ i, 1 ≤ m i) (hx0 : ∀ i, x i 0 = u i)
    (hxm : ∀ i, x i (m i) = v i) (hxZ : ∀ i, pimg (m i + 1) (x i) ⊆ Z i)
    (noPar : ∀ i j, i ≠ j → ¬ ((u i = u j ∧ v i = v j) ∨ (u i = v j ∧ v i = u j)))
    (noK2 : ∀ i, ∃ j, j ≠ i ∧ (u j = u i ∨ v j = u i ∨ u j = v i ∨ v j = v i)) :
    3 + Fintype.card ι ≤ 3 * Vp.card := by
  have hle := fun i => loop_erase (m i) (x i) (hm i) (by rw [hx0, hxm]; exact huv i)
  choose n y hS hy0 hyl himg using hle
  have hW : ∀ i, pimg (n i) (y i) ⊆ Z i := fun i => (himg i).trans (hxZ i)
  have hpZ : ∀ i k, k < n i → y i k ∈ Z i := fun i k hk => hW i (pt_mem_pimg (hS i).len hk)
  have hy0' : ∀ i, y i 0 = u i := fun i => (hy0 i).trans (hx0 i)
  have hyl' : ∀ i, y i (n i - 1) = v i := fun i => (hyl i).trans (hxm i)
  have hinner : ∀ i k, 0 < k → k + 1 < n i → y i k ∉ Vp := by
    intro i k h0 h1 hk
    rcases hZV i _ hk (hpZ i k (by omega)) with h | h
    · rw [← hy0' i] at h
      have := (hS i).nodup k 0 (by omega) (by omega) h
      omega
    · rw [← hyl' i] at h
      have := (hS i).nodup k (n i - 1) (by omega) (by omega) h
      omega
  let X : PLD ι :=
    { Vp := Vp
      n := n
      pt := y
      len := fun i => (hS i).len
      nodup := fun i => (hS i).nodup
      end0 := fun i => by rw [hy0']; exact hu i
      end1 := fun i => by rw [hyl']; exact hv i
      inner := hinner
      bend := by
        intro i j k l hij h0 h1 hl e
        exact hinner i k h0 h1 (hZ i j hij _ (hpZ i k (by omega)) (e ▸ hpZ j l hl))
      simple := fun i => (hS i).simple
      consec := fun i => (hS i).consec
      cross := by
        intro i j k l hij hk hl q h1 h2
        exact hZ i j hij q (hW i ⟨k, hk, h1⟩) (hW j ⟨l, hl, h2⟩)
      vavoid := by
        intro i k hk w hw hseg
        have hS' := hS i
        rcases hZV i w hw (hW i ⟨k, hk, hseg⟩) with h | h
        · rw [← hy0' i] at h
          subst h
          rcases Nat.lt_or_ge k 2 with hk2 | hk2
          · interval_cases k
            · exact Or.inl rfl
            · have := hS'.consec 0 (by omega) _ (left_mem_segment ℝ _ _) hseg
              exact absurd (hS'.nodup 0 1 (by omega) (by omega) this) (by omega)
          · exact absurd hseg (hS'.simple 0 k (by omega) hk _ (left_mem_segment ℝ _ _))
        · rw [← hyl' i] at h
          subst h
          have hl := hS'.len
          by_cases e1 : k + 1 = n i - 1
          · exact Or.inr (by rw [e1])
          · by_cases e2 : k + 2 = n i - 1
            · have hr : y i (n i - 1) ∈ segment ℝ (y i (k + 1)) (y i (k + 2)) := by
                rw [← e2]; exact right_mem_segment ℝ _ _
              have := hS'.consec k (by omega) _ hseg hr
              exact absurd (hS'.nodup (n i - 1) (k + 1) (by omega) (by omega) this) (by omega)
            · have hr : y i (n i - 1) ∈ segment ℝ (y i (n i - 2)) (y i (n i - 2 + 1)) := by
                rw [show n i - 2 + 1 = n i - 1 by omega]; exact right_mem_segment ℝ _ _
              exact absurd hr (hS'.simple k (n i - 2) (by omega) (by omega) _ hseg)
      noPar := by
        intro i j hij h
        rw [hy0', hy0', hyl', hyl'] at h
        exact noPar i j hij h
      noK2 := by
        intro i
        obtain ⟨j, hj, h⟩ := noK2 i
        refine ⟨j, hj, ?_⟩
        rw [hy0', hy0', hyl', hyl']
        exact h }
  exact X.edge_bound


/-! ## M9a: the K2 reduction and the glue from tubes to `EdgeBoundFor` -/

/-- Edges `e` and `f` share an endpoint. -/
def Shares {N M : ℕ} (D : PlaneDrawing N M) (e f : Fin M) : Prop :=
  D.left f = D.left e ∨ D.right f = D.left e ∨ D.left f = D.right e ∨ D.right f = D.right e

theorem shares_symm {N M : ℕ} (D : PlaneDrawing N M) {e f : Fin M} (h : Shares D e f) :
    Shares D f e := by
  unfold Shares at *
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

/-- The analytic input: raw polylines inside tubes that meet only at real vertices. -/
def Tubes {N M : ℕ} (D : PlaneDrawing N M) (V : Finset (Fin N)) (E : Finset (Fin M)) : Prop :=
  ∃ (Z : {e // e ∈ E} → Set E2) (m : {e // e ∈ E} → ℕ) (x : {e // e ∈ E} → ℕ → E2),
    (∀ i j, i ≠ j → ∀ q, q ∈ Z i → q ∈ Z j → ∃ w ∈ V, D.vertex w = q) ∧
    (∀ i, ∀ w ∈ V, D.vertex w ∈ Z i → w = D.left i.1 ∨ w = D.right i.1) ∧
    (∀ i, 1 ≤ m i) ∧ (∀ i, x i 0 = D.vertex (D.left i.1)) ∧
    (∀ i, x i (m i) = D.vertex (D.right i.1)) ∧ (∀ i, pimg (m i + 1) (x i) ⊆ Z i)

theorem core_of_tubes {N M : ℕ} (D : PlaneDrawing N M) (V : Finset (Fin N)) (E : Finset (Fin M))
    (hend : ∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V)
    (hK2 : ∀ e ∈ E, ∃ f ∈ E, f ≠ e ∧ Shares D e f) (hne : E.Nonempty) (hT : Tubes D V E) :
    3 + E.card ≤ 3 * V.card := by
  classical
  obtain ⟨Z, m, x, hZ, hZV, hm, hx0, hxm, hxZ⟩ := hT
  haveI : Nonempty {e // e ∈ E} := ⟨⟨_, hne.choose_spec⟩⟩
  have vi := D.vertex_injective
  have h := edge_bound_of_tubes (ι := {e // e ∈ E}) (V.image D.vertex)
    (fun i => D.vertex (D.left i.1)) (fun i => D.vertex (D.right i.1))
    (fun i e => D.no_loop i.1 (vi e))
    (fun i => Finset.mem_image_of_mem _ (hend i.1 i.2).1)
    (fun i => Finset.mem_image_of_mem _ (hend i.1 i.2).2)
    Z (fun i j hij q h1 h2 => by
      obtain ⟨w, hw, rfl⟩ := hZ i j hij q h1 h2
      exact Finset.mem_image_of_mem _ hw)
    (fun i w hw hwZ => by
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
      rcases hZV i w' hw' hwZ with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h]))
    m x hm hx0 hxm hxZ
    (fun i j hij h => by
      apply D.no_parallel i.1 j.1 (fun e => hij (Subtype.ext e))
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨vi h1, vi h2⟩
      · exact Or.inr ⟨vi h1, vi h2⟩)
    (fun i => by
      obtain ⟨f, hf, hfi, hs⟩ := hK2 i.1 i.2
      refine ⟨⟨f, hf⟩, fun e => hfi (congrArg Subtype.val e), ?_⟩
      rcases hs with h | h | h | h
      · exact Or.inl (by simp only [h])
      · exact Or.inr (Or.inl (by simp only [h]))
      · exact Or.inr (Or.inr (Or.inl (by simp only [h])))
      · exact Or.inr (Or.inr (Or.inr (by simp only [h]))))
  rw [Fintype.card_coe, Finset.card_image_of_injective _ vi] at h
  exact h

/-- The K2 reduction: the core bound for K2-free nonempty edge sets gives the full edge bound. -/
theorem edgeBound_of_core {N M : ℕ} (D : PlaneDrawing N M)
    (core : ∀ (V : Finset (Fin N)) (E : Finset (Fin M)), (∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V) →
      FreeSet D E → (∀ e ∈ E, ∃ f ∈ E, f ≠ e ∧ Shares D e f) → E.Nonempty →
      3 + E.card ≤ 3 * V.card) :
    EdgeBoundFor D := by
  classical
  intro V E hend hfree
  let P : Fin M → Prop := fun e => ∃ f ∈ E, f ≠ e ∧ Shares D e f
  let E' := E.filter P
  let K := E.filter (fun e => ¬ P e)
  let W := K.biUnion (fun e => ({D.left e, D.right e} : Finset (Fin N)))
  have hEK : E'.card + K.card = E.card := Finset.card_filter_add_card_filter_not P
  have hKiso : ∀ k ∈ K, ∀ e ∈ E, e ≠ k → ¬ Shares D k e := by
    intro k hk e he hne hs
    exact (Finset.mem_filter.mp hk).2 ⟨e, he, hne, hs⟩
  have hW : W.card = 2 * K.card := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun e _ => Finset.card_pair (D.no_loop e)), Finset.sum_const,
        smul_eq_mul, mul_comm]
    · intro e he f hf hef
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro a ha ha'
      apply hKiso e (Finset.mem_coe.mp he) f (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).1
        (Ne.symm hef)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha'
      unfold Shares
      rcases ha with rfl | rfl <;> rcases ha' with h | h <;> tauto
  have hWV : W ⊆ V := by
    intro a ha
    obtain ⟨e, he, ha⟩ := Finset.mem_biUnion.mp ha
    have := hend e (Finset.mem_filter.mp he).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact this.1
    · exact this.2
  have hE'V : ∀ e ∈ E', D.left e ∈ V \ W ∧ D.right e ∈ V \ W := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have hv := hend e he'.1
    have hnot : ∀ a, (a = D.left e ∨ a = D.right e) → a ∉ W := by
      intro a ha haW
      obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp haW
      have hke : e ≠ k := by
        intro h
        rw [h] at he'
        exact (Finset.mem_filter.mp hk).2 he'.2
      apply hKiso k hk e he'.1 hke
      simp only [Finset.mem_insert, Finset.mem_singleton] at hak
      unfold Shares
      rcases ha with rfl | rfl <;> rcases hak with h | h <;> tauto
    exact ⟨Finset.mem_sdiff.mpr ⟨hv.1, hnot _ (Or.inl rfl)⟩,
      Finset.mem_sdiff.mpr ⟨hv.2, hnot _ (Or.inr rfl)⟩⟩
  have hfree' : FreeSet D E' := fun e he f hf =>
    hfree e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have hVW : (V \ W).card = V.card - W.card := Finset.card_sdiff_of_subset hWV
  have hWle : W.card ≤ V.card := Finset.card_le_card hWV
  by_cases hne : E'.Nonempty
  · have hK2 : ∀ e ∈ E', ∃ f ∈ E', f ≠ e ∧ Shares D e f := by
      intro e he
      obtain ⟨f, hf, hfe, hs⟩ := (Finset.mem_filter.mp he).2
      exact ⟨f, Finset.mem_filter.mpr ⟨hf, e, (Finset.mem_filter.mp he).1, Ne.symm hfe,
        shares_symm D hs⟩, hfe, hs⟩
    have := core (V \ W) E' hE'V hfree' hK2 hne
    omega
  · have : E'.card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp hne
    omega

/-- Everything but the analytic tube construction. -/
theorem edgeBound_of_tubes {N M : ℕ} (D : PlaneDrawing N M)
    (hT : ∀ (V : Finset (Fin N)) (E : Finset (Fin M)), (∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V) →
      FreeSet D E → Tubes D V E) :
    EdgeBoundFor D :=
  edgeBound_of_core D (fun V E hend hfree hK2 hne =>
    core_of_tubes D V E hend hK2 hne (hT V E hend hfree))


/-! ## M8b-1: spokes (straight segments from a vertex to its sphere of radius r) -/

theorem spoke_param {u p q : E2} (hq : q ∈ segment ℝ u p) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q = u + t • (p - u) := by
  rw [segment_eq_image', Set.mem_image] at hq
  obtain ⟨t, ⟨h0, h1⟩, rfl⟩ := hq
  exact ⟨t, h0, h1, rfl⟩

theorem spoke_dist {u p : E2} {t : ℝ} (ht : 0 ≤ t) : dist (u + t • (p - u)) u = t * dist p u := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

theorem spoke_sub_ball {u p : E2} {r : ℝ} (hp : dist p u ≤ r) :
    segment ℝ u p ⊆ Metric.closedBall u r :=
  (convex_closedBall u r).segment_subset
    (Metric.mem_closedBall_self (le_trans dist_nonneg hp)) (Metric.mem_closedBall.mpr hp)

/-- The only point of a spoke on the sphere is its outer end. -/
theorem spoke_sphere {u p q : E2} {r : ℝ} (hr : 0 < r) (hp : dist p u = r)
    (hq : q ∈ segment ℝ u p) (hqr : r ≤ dist q u) : q = p := by
  obtain ⟨t, h0, h1, rfl⟩ := spoke_param hq
  rw [spoke_dist h0, hp] at hqr
  have ht : t = 1 := le_antisymm h1 (by
    by_contra h
    rw [not_le] at h
    have := mul_lt_mul_of_pos_right h hr
    linarith)
  rw [ht, one_smul, add_sub_cancel]

/-- Two spokes to distinct sphere points meet only at the center. -/
theorem spoke_inter {u p p' q : E2} {r : ℝ} (hr : 0 < r) (hp : dist p u = r) (hp' : dist p' u = r)
    (hne : p ≠ p') (hq : q ∈ segment ℝ u p) (hq' : q ∈ segment ℝ u p') : q = u := by
  obtain ⟨t, h0, _, rfl⟩ := spoke_param hq
  obtain ⟨s, h0', _, hs⟩ := spoke_param hq'
  have hd := congrArg (fun z => dist z u) hs
  simp only at hd
  rw [spoke_dist h0, spoke_dist h0', hp, hp'] at hd
  have hts : t = s := by
    have := mul_right_cancel₀ hr.ne' hd
    exact this
  subst hts
  by_cases ht0 : t = 0
  · rw [ht0, zero_smul, add_zero]
  · exfalso
    apply hne
    have h2 : t • (p - u) = t • (p' - u) := add_left_cancel hs
    have h3 := smul_right_injective E2 ht0 h2
    simpa using h3


/-! ## M8b-2: a clearance radius -/

theorem exists_pos_lb {α : Type*} [Fintype α] (f : α → ℝ) (hf : ∀ a, 0 < f a) :
    ∃ c > 0, ∀ a, c ≤ f a := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨1, one_pos, fun a => (IsEmpty.false a).elim⟩
  · obtain ⟨a0, _, h⟩ := Finset.univ.exists_min_image f Finset.univ_nonempty
    exact ⟨f a0, hf a0, fun a => h a (Finset.mem_univ a)⟩

theorem arc_ne_vertex {N M : ℕ} (D : PlaneDrawing N M) {e : Fin M} {w : Fin N}
    (h1 : w ≠ D.left e) (h2 : w ≠ D.right e) (t : EdgeParameter) : D.arc e t ≠ D.vertex w := by
  by_cases ht0 : t.val = 0
  · have : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext ht0
    rw [this, D.start]
    exact fun h => h1 (D.vertex_injective h).symm
  · by_cases ht1 : t.val = 1
    · have : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht1
      rw [this, D.finish]
      exact fun h => h2 (D.vertex_injective h).symm
    · exact D.avoid_vertices e t (lt_of_le_of_ne t.2.1 (Ne.symm ht0)) (lt_of_le_of_ne t.2.2 ht1) w

theorem arc_clear {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M) (w : Fin N)
    (h1 : w ≠ D.left e) (h2 : w ≠ D.right e) :
    ∃ c > 0, ∀ t, c ≤ dist (D.arc e t) (D.vertex w) := by
  have hc : Continuous (fun t => dist (D.arc e t) (D.vertex w)) :=
    (D.continuous_arc e).dist continuous_const
  obtain ⟨t0, _, ht0⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨0, by constructor <;> norm_num⟩ : EdgeParameter), Set.mem_univ _⟩ hc.continuousOn
  exact ⟨_, dist_pos.mpr (arc_ne_vertex D h1 h2 t0), fun t => ht0 (Set.mem_univ t)⟩

/-- A radius `r` such that distinct vertices are `3r` apart and every arc stays `3r` away from
the vertices it is not incident to. -/
theorem clearance {N M : ℕ} (D : PlaneDrawing N M) : ∃ r > 0,
    (∀ a b : Fin N, a ≠ b → 3 * r < dist (D.vertex a) (D.vertex b)) ∧
    (∀ e : Fin M, ∀ w : Fin N, w ≠ D.left e → w ≠ D.right e → ∀ t,
      3 * r < dist (D.arc e t) (D.vertex w)) := by
  classical
  obtain ⟨c1, hc1, h1⟩ := exists_pos_lb
    (fun ab : Fin N × Fin N => if ab.1 = ab.2 then 1 else dist (D.vertex ab.1) (D.vertex ab.2))
    (by
      intro ab
      dsimp only
      split_ifs with h
      · exact one_pos
      · exact dist_pos.mpr (fun e => h (D.vertex_injective e)))
  have hce : ∀ ew : Fin M × Fin N, ∃ c > 0, (ew.2 ≠ D.left ew.1 → ew.2 ≠ D.right ew.1 →
      ∀ t, c ≤ dist (D.arc ew.1 t) (D.vertex ew.2)) := by
    intro ew
    by_cases h : ew.2 ≠ D.left ew.1 ∧ ew.2 ≠ D.right ew.1
    · obtain ⟨c, hc, hct⟩ := arc_clear D ew.1 ew.2 h.1 h.2
      exact ⟨c, hc, fun _ _ => hct⟩
    · exact ⟨1, one_pos, fun a b => absurd ⟨a, b⟩ h⟩
  choose c hc hct using hce
  obtain ⟨c2, hc2, h2⟩ := exists_pos_lb c hc
  have hm : 0 < min c1 c2 := lt_min hc1 hc2
  refine ⟨min c1 c2 / 4, by positivity, ?_, ?_⟩
  · intro a b hab
    have h := h1 (a, b)
    simp only [hab, if_false] at h
    have := min_le_left c1 c2
    linarith
  · intro e w hw1 hw2 t
    have := hct (e, w) hw1 hw2 t
    have := h2 (e, w)
    have := min_le_right c1 c2
    linarith



/-! ## M8b-3: the extended arc, last exit and first entry -/

/-- The arc of `e`, extended to all of `ℝ` (constant outside `[0,1]`). -/
noncomputable def gam {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M) : ℝ → E2 :=
  Set.IccExtend (zero_le_one' ℝ) (D.arc e)

theorem gam_cont {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M) : Continuous (gam D e) :=
  (D.continuous_arc e).Icc_extend'

theorem gam_zero {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M) :
    gam D e 0 = D.vertex (D.left e) := by
  unfold gam
  rw [Set.IccExtend_left]
  exact D.start e

theorem gam_one {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M) :
    gam D e 1 = D.vertex (D.right e) := by
  unfold gam
  rw [Set.IccExtend_right]
  exact D.finish e

theorem gam_free {N M : ℕ} {D : PlaneDrawing N M} {E : Finset (Fin M)} (hfree : FreeSet D E)
    {e f : Fin M} (he : e ∈ E) (hf : f ∈ E) (hef : e ≠ f) {t s : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hs0 : 0 < s) (hs1 : s < 1) : gam D e t ≠ gam D f s := by
  unfold gam
  rw [Set.IccExtend_of_mem _ _ ⟨ht0.le, ht1.le⟩, Set.IccExtend_of_mem _ _ ⟨hs0.le, hs1.le⟩]
  exact hfree e he f hf hef _ _ ht0 ht1 hs0 hs1

/-- Last exit from the ball at the left end, first entry into the ball at the right end. -/
theorem exit_entry {N M : ℕ} (D : PlaneDrawing N M) {r : ℝ} (hr : 0 < r)
    (hV : ∀ a b : Fin N, a ≠ b → 3 * r < dist (D.vertex a) (D.vertex b))
    (hA : ∀ e : Fin M, ∀ w : Fin N, w ≠ D.left e → w ≠ D.right e → ∀ t,
      3 * r < dist (D.arc e t) (D.vertex w)) (e : Fin M) :
    ∃ τ σ : ℝ, 0 < τ ∧ τ ≤ σ ∧ σ < 1 ∧
      dist (gam D e τ) (D.vertex (D.left e)) = r ∧ dist (gam D e σ) (D.vertex (D.right e)) = r ∧
      (∀ t ∈ Set.Icc τ σ, ∀ w, r ≤ dist (gam D e t) (D.vertex w)) := by
  set g := gam D e with hg
  set u := D.vertex (D.left e) with hu
  set v := D.vertex (D.right e) with hv
  have gc : Continuous g := gam_cont D e
  have g0 : g 0 = u := gam_zero D e
  have g1 : g 1 = v := gam_one D e
  have huv : 3 * r < dist u v := hV _ _ (D.no_loop e)
  have hfar : ∀ t w, w ≠ D.left e → w ≠ D.right e → 3 * r < dist (g t) (D.vertex w) :=
    fun t w h1 h2 => hA e w h1 h2 _
  have fuc : Continuous (fun t => dist (g t) u) := gc.dist continuous_const
  have fvc : Continuous (fun t => dist (g t) v) := gc.dist continuous_const
  -- last exit from closedBall u r
  have hSc : IsCompact (Set.Icc (0 : ℝ) 1 ∩ g ⁻¹' Metric.closedBall u r) :=
    isCompact_Icc.inter_right (Metric.isClosed_closedBall.preimage gc)
  obtain ⟨τ, ⟨hτI, hτB⟩, hτmax⟩ := hSc.exists_isGreatest
    ⟨0, ⟨le_refl _, zero_le_one⟩, by
      rw [Set.mem_preimage, g0, Metric.mem_closedBall, dist_self]; exact hr.le⟩
  rw [Set.mem_preimage, Metric.mem_closedBall] at hτB
  have hafter : ∀ t, τ < t → t ≤ 1 → r < dist (g t) u := by
    intro t h1 h2
    by_contra h
    rw [not_lt] at h
    have := hτmax ⟨⟨by linarith [hτI.1], h2⟩, Metric.mem_closedBall.mpr h⟩
    linarith
  have hτ1 : τ < 1 := by
    rcases lt_or_eq_of_le hτI.2 with h | h
    · exact h
    · exfalso
      rw [h, g1, dist_comm] at hτB
      linarith
  have hτr : dist (g τ) u = r := by
    have h1 : r ≤ dist (g 1) u := by rw [g1, dist_comm]; linarith
    obtain ⟨c, hc, hcr⟩ := intermediate_value_Icc hτI.2 fuc.continuousOn ⟨hτB, h1⟩
    rcases eq_or_lt_of_le hc.1 with h | h
    · rw [h]; exact hcr
    · exact absurd hcr (ne_of_gt (hafter c h hc.2))
  have hτ0 : 0 < τ := by
    rcases eq_or_lt_of_le hτI.1 with h | h
    · rw [← h, g0, dist_self] at hτr
      linarith
    · exact h
  -- first entry into closedBall v r after τ
  have hSc' : IsCompact (Set.Icc τ 1 ∩ g ⁻¹' Metric.closedBall v r) :=
    isCompact_Icc.inter_right (Metric.isClosed_closedBall.preimage gc)
  obtain ⟨σ, ⟨hσI, hσB⟩, hσmin⟩ := hSc'.exists_isLeast
    ⟨1, ⟨hτ1.le, le_refl _⟩, by
      rw [Set.mem_preimage, g1, Metric.mem_closedBall, dist_self]; exact hr.le⟩
  rw [Set.mem_preimage, Metric.mem_closedBall] at hσB
  have hbefore : ∀ t, τ ≤ t → t < σ → r < dist (g t) v := by
    intro t h1 h2
    by_contra h
    rw [not_lt] at h
    have := hσmin ⟨⟨h1, by linarith [hσI.2]⟩, Metric.mem_closedBall.mpr h⟩
    linarith
  have hτv : 2 * r < dist (g τ) v := by
    have := dist_triangle u (g τ) v
    rw [dist_comm u (g τ), hτr] at this
    linarith
  have hσr : dist (g σ) v = r := by
    obtain ⟨c, hc, hcr⟩ := intermediate_value_Icc' hσI.1 fvc.continuousOn ⟨hσB, by linarith⟩
    rcases eq_or_lt_of_le hc.2 with h | h
    · rw [← h]; exact hcr
    · exact absurd hcr (ne_of_gt (hbefore c hc.1 h))
  have hσ1 : σ < 1 := by
    rcases lt_or_eq_of_le hσI.2 with h | h
    · exact h
    · exfalso
      rw [h, g1, dist_self] at hσr
      linarith
  refine ⟨τ, σ, hτ0, hσI.1, hσ1, hτr, hσr, ?_⟩
  intro t ht w
  by_cases hw1 : w = D.left e
  · rw [hw1, ← hu]
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hτr]
    · exact (hafter t h (by linarith [ht.2])).le
  · by_cases hw2 : w = D.right e
    · rw [hw2, ← hv]
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h, hσr]
      · exact (hbefore t ht.1 h).le
    · linarith [hfar t w hw1 hw2]


/-! ## M8b-4: an inscribed polyline with spokes at both ends -/

theorem polyline {g : ℝ → E2} (gc : Continuous g) {τ σ ε : ℝ} (hτσ : τ ≤ σ) (hε : 0 < ε)
    (u v : E2) :
    ∃ m : ℕ, ∃ x : ℕ → E2, 1 ≤ m ∧ x 0 = u ∧ x m = v ∧
      pimg (m + 1) x ⊆
        segment ℝ u (g τ) ∪ Metric.cthickening ε (g '' Set.Icc τ σ) ∪ segment ℝ v (g σ) := by
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous gc.continuousOn) ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt ((σ - τ) / η)
  have hL0 : (0 : ℝ) < L := lt_of_le_of_lt (div_nonneg (by linarith) hη.le) hL
  set h := (σ - τ) / L with hh
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hL0.le
  have hhη : h < η := by
    rw [hh, div_lt_iff₀ hL0]
    rw [div_lt_iff₀ hη] at hL
    linarith
  have hLh : (L : ℝ) * h = σ - τ := by
    rw [hh]
    field_simp
  let x : ℕ → E2 := fun k => if k = 0 then u else if k < L + 2 then g (τ + ((k : ℝ) - 1) * h) else v
  have hx0 : x 0 = u := if_pos rfl
  have hxL : x (L + 2) = v := by
    show (if L + 2 = 0 then u else if L + 2 < L + 2 then _ else v) = v
    rw [if_neg (by omega), if_neg (lt_irrefl _)]
  have hxk : ∀ k, 0 < k → k < L + 2 → x k = g (τ + ((k : ℝ) - 1) * h) := by
    intro k h0 h1
    show (if k = 0 then u else if k < L + 2 then _ else v) = _
    rw [if_neg (by omega), if_pos h1]
  refine ⟨L + 2, x, by omega, hx0, hxL, ?_⟩
  rintro q ⟨k, hk, hq⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [hx0, hxk 1 one_pos (by omega)] at hq
    simp only [Nat.cast_one, sub_self, zero_mul, add_zero] at hq
    exact Or.inl (Or.inl hq)
  · by_cases hkL : k = L + 1
    · subst hkL
      rw [hxk (L + 1) (by omega) (by omega), hxL] at hq
      have e1 : τ + (((L + 1 : ℕ) : ℝ) - 1) * h = σ := by
        push_cast
        linarith
      rw [e1, segment_symm] at hq
      exact Or.inr hq
    · rw [hxk k hk0 (by omega), hxk (k + 1) (by omega) (by omega)] at hq
      refine Or.inl (Or.inr ?_)
      have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have hkL' : (k : ℝ) ≤ L := by exact_mod_cast (show k ≤ L by omega)
      set a := τ + ((k : ℝ) - 1) * h with ha
      set b := τ + (((k + 1 : ℕ) : ℝ) - 1) * h with hb
      have hb' : b = τ + (k : ℝ) * h := by rw [hb]; push_cast; ring
      have hm1 : 0 ≤ ((k : ℝ) - 1) * h := mul_nonneg (by linarith) hh0
      have hm2 : ((k : ℝ) - 1) * h ≤ L * h := mul_le_mul_of_nonneg_right (by linarith) hh0
      have hm3 : 0 ≤ (k : ℝ) * h := mul_nonneg (by linarith) hh0
      have hm4 : (k : ℝ) * h ≤ L * h := mul_le_mul_of_nonneg_right hkL' hh0
      have haI : a ∈ Set.Icc τ σ := ⟨by rw [ha]; linarith, by rw [ha]; linarith⟩
      have hbI : b ∈ Set.Icc τ σ := ⟨by rw [hb']; linarith, by rw [hb']; linarith⟩
      have hab : dist a b < η := by
        rw [Real.dist_eq, hb', ha, show τ + ((k : ℝ) - 1) * h - (τ + k * h) = -h by ring, abs_neg,
          abs_of_nonneg hh0]
        exact hhη
      have hgab := hU a haI b hbI hab
      have hsub : segment ℝ (g a) (g b) ⊆ Metric.closedBall (g a) ε :=
        (convex_closedBall (g a) ε).segment_subset (Metric.mem_closedBall_self hε.le)
          (Metric.mem_closedBall.mpr (by rw [dist_comm]; exact hgab.le))
      exact Metric.closedBall_subset_cthickening (Set.mem_image_of_mem g haI) ε (hsub hq)


/-! ## M8b-5: the tubes exist -/

theorem tubes_exist {N M : ℕ} (D : PlaneDrawing N M) (V : Finset (Fin N)) (E : Finset (Fin M))
    (hend : ∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V) (hfree : FreeSet D E) : Tubes D V E := by
  classical
  obtain ⟨r, hr, hV, hA⟩ := clearance D
  choose τ σ hτ0 hτσ hσ1 hτr hσr hK using fun e => exit_entry D hr hV hA e
  let K : Fin M → Set E2 := fun e => gam D e '' Set.Icc (τ e) (σ e)
  let Sp : Fin M → Set E2 := fun e =>
    segment ℝ (D.vertex (D.left e)) (gam D e (τ e)) ∪ segment ℝ (D.vertex (D.right e)) (gam D e (σ e))
  have hKc : ∀ e, IsCompact (K e) := fun e => isCompact_Icc.image (gam_cont D e)
  have hSpc : ∀ e, IsClosed (Sp e) := fun e => (seg_closed _ _).union (seg_closed _ _)
  have hSp : ∀ e z, z ∈ Sp e → ∃ a s, (a = D.left e ∨ a = D.right e) ∧ 0 < s ∧ s < 1 ∧
      dist (gam D e s) (D.vertex a) = r ∧ z ∈ segment ℝ (D.vertex a) (gam D e s) := by
    intro e z hz
    rcases hz with hz | hz
    · exact ⟨D.left e, τ e, Or.inl rfl, hτ0 e, by linarith [hτσ e, hσ1 e], hτr e, hz⟩
    · exact ⟨D.right e, σ e, Or.inr rfl, by linarith [hτ0 e, hτσ e], hσ1 e, hσr e, hz⟩
  have hKC : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (K e) (Sp f ∪ K f) := by
    intro e he f hf hef
    rw [Set.disjoint_left]
    rintro z ⟨t, ht, rfl⟩ hz
    have ht0 : 0 < t := by linarith [ht.1, hτ0 e]
    have ht1 : t < 1 := by linarith [ht.2, hσ1 e]
    rcases hz with hz | ⟨s, hs, hzs⟩
    · obtain ⟨a, s, -, hs0, hs1, hsr, hzs⟩ := hSp f _ hz
      exact gam_free hfree he hf hef ht0 ht1 hs0 hs1 (spoke_sphere hr hsr hzs (hK e t ht a))
    · exact gam_free hfree he hf hef ht0 ht1 (by linarith [hs.1, hτ0 f])
        (by linarith [hs.2, hσ1 f]) hzs.symm
  have hδ : ∀ ef : {e // e ∈ E} × {e // e ∈ E}, ∃ δ > 0, ef.1 ≠ ef.2 →
      Disjoint (Metric.cthickening δ (K ef.1.1)) (Metric.cthickening δ (Sp ef.2.1 ∪ K ef.2.1)) := by
    intro ef
    by_cases h : ef.1 = ef.2
    · exact ⟨1, one_pos, fun h' => absurd h h'⟩
    · obtain ⟨δ, hδ, hd⟩ := (hKC _ ef.1.2 _ ef.2.2 (fun e => h (Subtype.ext e))).exists_cthickenings
        (hKc _) ((hSpc _).union (hKc _).isClosed)
      exact ⟨δ, hδ, fun _ => hd⟩
  choose δ hδ0 hδd using hδ
  obtain ⟨δ0, hδ0pos, hδ0le⟩ := exists_pos_lb δ hδ0
  set ε := min δ0 (r / 2) with hε
  have hε0 : 0 < ε := lt_min hδ0pos (by linarith)
  have hεδ : ∀ ef, ε ≤ δ ef := fun ef => (min_le_left _ _).trans (hδ0le ef)
  have hεr : ε < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcth : ∀ e z, z ∈ Metric.cthickening ε (K e) →
      ∃ t ∈ Set.Icc (τ e) (σ e), dist z (gam D e t) ≤ ε := by
    intro e z hz
    rw [(hKc e).cthickening_eq_biUnion_closedBall hε0.le] at hz
    simp only [Set.mem_iUnion, Metric.mem_closedBall] at hz
    obtain ⟨_, ⟨t, ht, rfl⟩, h⟩ := hz
    exact ⟨t, ht, h⟩
  have hX : ∀ i j : {e // e ∈ E}, i ≠ j → ∀ z, z ∈ Metric.cthickening ε (K i.1) →
      z ∈ Sp j.1 ∪ Metric.cthickening ε (K j.1) → False := by
    intro i j hij z h1 h2
    apply Set.disjoint_left.mp (hδd (i, j) hij) (Metric.cthickening_mono (hεδ (i, j)) _ h1)
    rcases h2 with h2 | h2
    · exact Metric.self_subset_cthickening _ (Or.inl h2)
    · exact Metric.cthickening_mono (hεδ (i, j)) _
        (Metric.cthickening_subset_of_subset _ Set.subset_union_right h2)
  choose m x hm hx0 hxm hxZ using fun e => polyline (gam_cont D e) (hτσ e) hε0
    (D.vertex (D.left e)) (D.vertex (D.right e))
  have hmem : ∀ e z, z ∈ segment ℝ (D.vertex (D.left e)) (gam D e (τ e)) ∪
      Metric.cthickening ε (K e) ∪ segment ℝ (D.vertex (D.right e)) (gam D e (σ e)) →
      z ∈ Sp e ∨ z ∈ Metric.cthickening ε (K e) := by
    rintro e z ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  refine ⟨fun i => segment ℝ (D.vertex (D.left i.1)) (gam D i.1 (τ i.1)) ∪
      Metric.cthickening ε (K i.1) ∪ segment ℝ (D.vertex (D.right i.1)) (gam D i.1 (σ i.1)),
    fun i => m i.1, fun i => x i.1, ?_, ?_, fun i => hm i.1, fun i => hx0 i.1,
    fun i => hxm i.1, fun i => hxZ i.1⟩
  · intro i j hij z hzi hzj
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    rcases hmem i.1 z hzi with h1 | h1
    · rcases hmem j.1 z hzj with h2 | h2
      · obtain ⟨a, s, ha, hs0, hs1, hsr, hza⟩ := hSp _ _ h1
        obtain ⟨b, s', hb, hs0', hs1', hsr', hzb⟩ := hSp _ _ h2
        have da := Metric.mem_closedBall.mp (spoke_sub_ball hsr.le hza)
        have db := Metric.mem_closedBall.mp (spoke_sub_ball hsr'.le hzb)
        by_cases hab : a = b
        · rw [← hab] at hsr' hzb
          refine ⟨a, ?_, (spoke_inter hr hsr hsr'
            (gam_free hfree i.2 j.2 hne hs0 hs1 hs0' hs1') hza hzb).symm⟩
          rcases ha with ha | ha
          · rw [ha]; exact (hend _ i.2).1
          · rw [ha]; exact (hend _ i.2).2
        · exfalso
          have h3 := hV a b hab
          have h4 := dist_triangle_left (D.vertex a) (D.vertex b) z
          linarith
      · exact (hX j i (Ne.symm hij) z h2 (Or.inl h1)).elim
    · exact (hX i j hij z h1 (hmem j.1 z hzj)).elim
  · intro i w _ hwZ
    rcases hwZ with (h | h) | h
    · have h1 := Metric.mem_closedBall.mp (spoke_sub_ball (hτr i.1).le h)
      by_contra hne
      rw [not_or] at hne
      linarith [hV w (D.left i.1) hne.1]
    · obtain ⟨t, ht, hd⟩ := hcth _ _ h
      have h1 := hK i.1 t ht w
      rw [dist_comm] at hd
      linarith
    · have h1 := Metric.mem_closedBall.mp (spoke_sub_ball (hσr i.1).le h)
      by_contra hne
      rw [not_or] at hne
      linarith [hV w (D.right i.1) hne.2]

/-- The edge bound (b2255bec) for every drawing. -/
theorem edgeBound {N M : ℕ} (D : PlaneDrawing N M) : EdgeBoundFor D :=
  edgeBound_of_tubes D (fun V E hend hfree => tubes_exist D V E hend hfree)


end CrB

set_option maxHeartbeats 4000000 in
open BookSixth in
theorem solution {N M : ℕ} (D : PlaneDrawing N M) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : p^2 * (M : ℝ) ≤ 3*p*(N : ℝ) + p^4*(D.crossings.card : ℝ) := by
  exact CrB.sampling_of_edgeBound D (CrB.edgeBound D) p hp hp1
