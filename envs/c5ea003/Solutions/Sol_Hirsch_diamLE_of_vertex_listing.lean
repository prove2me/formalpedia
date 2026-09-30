-- Prove2me | solution 1 for Hirsch.diamLE_of_vertex_listing
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T08:26:54.751482+00:00
-- url     : https://prove2.me/submissions/82315c0a-1ccc-4acb-a030-7c3c82b55549

import Theorems.Thm_Hirsch_graph_connected_general
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Hirsch
open scoped Classical

noncomputable section

variable {d n : ℕ}

theorem extreme_of_adj {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) :
    u ∈ extremePoints ℝ P := by
  have hseg : IsExtreme ℝ P (segment ℝ u v) := h.2
  have huP : u ∈ P := hseg.1 (left_mem_segment ℝ u v)
  refine mem_extremePoints_iff_left.2 ⟨huP, ?_⟩
  intro x1 hx1 x2 hx2 hop
  have hx1s : x1 ∈ segment ℝ u v :=
    hseg.left_mem_of_mem_openSegment hx1 hx2 (left_mem_segment ℝ u v) hop
  have hx2s : x2 ∈ segment ℝ u v :=
    hseg.right_mem_of_mem_openSegment hx1 hx2 (left_mem_segment ℝ u v) hop
  rw [segment_eq_image ℝ u v] at hx1s hx2s
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hx1s
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx2s
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hop
  have hexp :
      a • ((1 - s) • u + s • v) + b • ((1 - t) • u + t • v) =
        (a * (1 - s) + b * (1 - t)) • u + (a * s + b * t) • v := by
    simp [smul_add, smul_smul, add_smul]
    abel
  rw [hexp] at hcomb
  have hcu : a * (1 - s) + b * (1 - t) = 1 - (a * s + b * t) := by
    calc
      a * (1 - s) + b * (1 - t) = a + b - (a * s + b * t) := by ring
      _ = 1 - (a * s + b * t) := by rw [hab]
  rw [hcu] at hcomb
  set c := a * s + b * t
  have : c • (v - u) = 0 := by
    have hlin : (1 - c) • u + c • v = u := hcomb
    have : u + c • (v - u) = u := by
      calc
        u + c • (v - u) = u + (c • v - c • u) := by simp [smul_sub]
        _ = (u - c • u) + c • v := by abel
        _ = (1 - c) • u + c • v := by rw [sub_smul, one_smul]
        _ = u := hlin
    exact add_eq_left.mp this
  have hc0 : c = 0 := by
    by_contra hcne
    have : v - u = 0 := (smul_eq_zero.mp this).resolve_left hcne
    exact h.1 (eq_of_sub_eq_zero this).symm
  have hs00 : s = 0 := by
    have : a * s = 0 := by
      have has : 0 ≤ a * s := mul_nonneg ha.le hs0
      have hbt : 0 ≤ b * t := mul_nonneg hb.le ht0
      have hcdef : c = a * s + b * t := rfl
      nlinarith
    exact (mul_eq_zero.mp this).resolve_left ha.ne'
  subst s
  simp

theorem extreme_of_adj_right {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) :
    v ∈ extremePoints ℝ P :=
  extreme_of_adj ⟨h.1.symm, by simpa [segment_symm] using h.2⟩

theorem walk_extreme {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {L : ℕ} (w : ℕ → E)
    (hu : w 0 ∈ extremePoints ℝ P)
    (hs : ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))) :
    ∀ i ≤ L, w i ∈ extremePoints ℝ P := by
  intro i hi
  induction i with
  | zero => simpa using hu
  | succ i ih =>
    have hi' : i < L := Nat.lt_of_succ_le hi
    have hprev := ih (Nat.le_of_lt hi')
    rcases hs i hi' with hstay | hadj
    · simpa [hstay.symm] using hprev
    · exact extreme_of_adj_right hadj

def spliceWalk {E : Type*} (w : ℕ → E) (i j : ℕ) : ℕ → E :=
  fun t => if t ≤ i then w t else w (t + (j - i))

theorem spliceWalk_start {E : Type*} (w : ℕ → E) (i j : ℕ) :
    spliceWalk w i j 0 = w 0 := by
  simp [spliceWalk]

theorem spliceWalk_end {E : Type*} (w : ℕ → E) {i j L : ℕ}
    (hij : i < j) (hjL : j < L) :
    spliceWalk w i j (L - (j - i)) = w L := by
  have hlen : i < L - (j - i) := by
    have : j - i ≤ L - i := Nat.sub_le_sub_right (Nat.le_of_lt hjL) i
    omega
  have : ¬ L - (j - i) ≤ i := Nat.not_le.mpr hlen
  simp [spliceWalk, this]
  have : L - (j - i) + (j - i) = L := Nat.sub_add_cancel (by omega)
  simp [this]

theorem spliceWalk_steps {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {L : ℕ} (w : ℕ → E) {i j : ℕ}
    (hij : i < j) (hjL : j < L)
    (hs : ∀ t < L, w t = w (t + 1) ∨ Adj P (w t) (w (t + 1)))
    (hrep : w i = w j) :
    ∀ t < L - (j - i),
      spliceWalk w i j t = spliceWalk w i j (t + 1) ∨
        Adj P (spliceWalk w i j t) (spliceWalk w i j (t + 1)) := by
  intro t ht
  by_cases ht1 : t + 1 ≤ i
  · have ht0 : t ≤ i := Nat.le_of_succ_le ht1
    have htL : t < L := by omega
    simpa [spliceWalk, ht0, ht1] using hs t htL
  · by_cases hti : t ≤ i
    · have hteq : t = i := by
        have : i < t + 1 := Nat.not_le.mp ht1
        exact le_antisymm hti (Nat.lt_succ_iff.mp this)
      subst t
      have hstep := hs j (by omega)
      have hleft : spliceWalk w i j i = w j := by
        simp [spliceWalk, hrep]
      have hright : spliceWalk w i j (i + 1) = w (j + 1) := by
        have : ¬ i + 1 ≤ i := Nat.not_le.mpr (Nat.lt_succ_self i)
        have hidx : i + 1 + (j - i) = j + 1 := by omega
        simp [spliceWalk, this, hidx]
      simpa [hleft, hright] using hstep
    · have hleft : spliceWalk w i j t = w (t + (j - i)) := by
        simp [spliceWalk, hti]
      have hright : spliceWalk w i j (t + 1) = w (t + 1 + (j - i)) := by
        have : ¬ t + 1 ≤ i := by omega
        simp [spliceWalk, this]
      have htL : t + (j - i) < L := by omega
      have hstep := hs (t + (j - i)) htL
      have hadd : t + (j - i) + 1 = t + 1 + (j - i) := by omega
      simpa [hleft, hright, hadd] using hstep

theorem padWalk {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {L B : ℕ} (_hLB : L ≤ B) (w : ℕ → E)
    (hs : ∀ t < L, w t = w (t + 1) ∨ Adj P (w t) (w (t + 1))) :
    ∀ t < B, w (min t L) = w (min (t + 1) L) ∨
      Adj P (w (min t L)) (w (min (t + 1) L)) := by
  intro t ht
  by_cases h1 : t + 1 ≤ L
  · have hi' : t < L := Nat.lt_of_succ_le h1
    have hmin_i : min t L = t := min_eq_left (Nat.le_of_lt hi')
    have hmin_i1 : min (t + 1) L = t + 1 := min_eq_left h1
    simpa [hmin_i, hmin_i1] using hs t hi'
  · have hmi : min t L = L := by omega
    have hmi1 : min (t + 1) L = L := by omega
    exact Or.inl (by simp [hmi, hmi1])

theorem idx_injective {m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (vertices : Fin m → EuclideanSpace ℝ (Fin d))
    (hcover : ∀ x ∈ extremePoints ℝ (Hpoly a b), ∃ j, vertices j = x) :
    Function.Injective
      (fun x : extremePoints ℝ (Hpoly a b) => Classical.choose (hcover x.1 x.2)) := by
  intro x y hxy
  have hx := Classical.choose_spec (hcover x.1 x.2)
  have hy := Classical.choose_spec (hcover y.1 y.2)
  apply Subtype.ext
  have hxj :
      Classical.choose (hcover x.1 x.2) = Classical.choose (hcover y.1 y.2) := hxy
  rw [hxj] at hx
  exact hx.symm.trans hy

theorem card_extreme_le {m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (vertices : Fin m → EuclideanSpace ℝ (Fin d))
    (hcover : ∀ x ∈ extremePoints ℝ (Hpoly a b), ∃ j, vertices j = x) :
    Nat.card (extremePoints ℝ (Hpoly a b)) ≤ m := by
  have hinj := idx_injective a b vertices hcover
  haveI : Finite (extremePoints ℝ (Hpoly a b)) := Finite.of_injective _ hinj
  have hle := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_fin] using hle

theorem exists_simple_walk {m L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (vertices : Fin m → EuclideanSpace ℝ (Fin d))
    (hcover : ∀ x ∈ extremePoints ℝ (Hpoly a b), ∃ j, vertices j = x)
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hu : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hs : ∀ i < L, w i = w (i + 1) ∨ Adj (Hpoly a b) (w i) (w (i + 1))) :
    ∃ L' ≤ m - 1, ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = w 0 ∧ w' L' = w L ∧
      ∀ i < L', w' i = w' (i + 1) ∨ Adj (Hpoly a b) (w' i) (w' (i + 1)) := by
  revert w
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro w hu hs
    by_cases hrep : ∃ i j, i < j ∧ j ≤ L ∧ w i = w j
    · obtain ⟨i, j, hij, hjL, hweq⟩ := hrep
      have hj' : j ≤ L := hjL
      rcases lt_or_eq_of_le hj' with hjLlt | hjLeq
      · have hlen : L - (j - i) < L := by omega
        have hs' := spliceWalk_steps (P := Hpoly a b) w hij hjLlt hs hweq
        obtain ⟨L', hL', w', hw'0, hw'L, hs''⟩ :=
          ih (L - (j - i)) hlen (spliceWalk w i j)
            (by simpa [spliceWalk_start] using hu) hs'
        refine ⟨L', hL', w', ?_, ?_, hs''⟩
        · simpa [spliceWalk_start] using hw'0
        · simpa [spliceWalk_end w hij hjLlt] using hw'L
      · subst j
        have hiL : i < L := hij
        have hs' : ∀ t < i, w t = w (t + 1) ∨ Adj (Hpoly a b) (w t) (w (t + 1)) := by
          intro t ht
          exact hs t (lt_trans ht hiL)
        obtain ⟨L', hL', w', hw'0, hw'L, hs''⟩ := ih i hiL w hu hs'
        exact ⟨L', hL', w', hw'0, by simpa [hweq] using hw'L, hs''⟩
    · push Not at hrep
      have hwext := walk_extreme w hu hs
      let φ : Fin (L + 1) → extremePoints ℝ (Hpoly a b) :=
        fun t => ⟨w t.val, hwext t.val (Nat.le_of_lt_succ t.isLt)⟩
      have hinj : Function.Injective φ := by
        intro t1 t2 hφ
        have hww : w t1.val = w t2.val := Subtype.ext_iff.mp hφ
        apply Fin.ext
        rcases lt_trichotomy t1.val t2.val with hlt | heq | hgt
        · have : t2.val ≤ L := Nat.le_of_lt_succ t2.isLt
          exact (hrep t1.val t2.val hlt this hww).elim
        · exact heq
        · have : t1.val ≤ L := Nat.le_of_lt_succ t1.isLt
          exact (hrep t2.val t1.val hgt this hww.symm).elim
      have hcard := card_extreme_le a b vertices hcover
      haveI : Finite (extremePoints ℝ (Hpoly a b)) :=
        Finite.of_injective _ (idx_injective a b vertices hcover)
      have hle := Nat.card_le_card_of_injective φ hinj
      have : L + 1 ≤ m := by
        have := (Nat.card_fin (L + 1) ▸ hle).trans hcard
        simpa using this
      have hL : L ≤ m - 1 := by omega
      exact ⟨L, hL, w, rfl, rfl, hs⟩

theorem solution {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (vertices : Fin m → EuclideanSpace ℝ (Fin d))
    (hcover : ∀ x ∈ extremePoints ℝ (Hpoly a b), ∃ j, vertices j = x) :
    DiamLE (Hpoly a b) (m - 1) := by
  intro u hu v hv
  obtain ⟨L, w, hw0, hwL, hs⟩ := graph_connected_general d n a b u v hu hv
  have hu0 : w 0 ∈ extremePoints ℝ (Hpoly a b) := by simpa [hw0] using hu
  obtain ⟨L', hL', w', hw'0, hw'L, hs'⟩ :=
    exists_simple_walk a b vertices hcover w hu0 hs
  refine ⟨fun t => w' (min t L'), ?_, ?_, ?_⟩
  · simp [hw'0, hw0]
  · simp [min_eq_right hL', hw'L, hwL]
  · exact padWalk hL' w' hs'
