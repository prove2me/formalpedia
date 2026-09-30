-- Prove2me | solution 1 for Hirsch.rank_selected_row_face_diameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T23:25:53.933145+00:00
-- url     : https://prove2.me/submissions/c227d208-25c5-48b1-b49b-e94788770bf1

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

namespace HirschProduct

lemma append_walk {E : Type*} (R : E → E → Prop)
    {u v z : E} {A B : ℕ}
    (p q : ℕ → E)
    (hp0 : p 0 = u) (hpA : p A = v)
    (hq0 : q 0 = v) (hqB : q B = z)
    (hp : ∀ j < A, p j = p (j + 1) ∨ R (p j) (p (j + 1)))
    (hq : ∀ j < B, q j = q (j + 1) ∨ R (q j) (q (j + 1))) :
    ∃ w : ℕ → E, w 0 = u ∧ w (A + B) = z ∧
      ∀ j < A + B, w j = w (j + 1) ∨ R (w j) (w (j + 1)) := by
  let w : ℕ → E := fun j => if j < A then p j else q (j - A)
  have hleft (j : ℕ) (hj : j ≤ A) : w j = p j := by
    by_cases h : j < A
    · simp only [w, if_pos h]
    · have heq : j = A := by omega
      subst j
      simp only [w, lt_self_iff_false, if_false, Nat.sub_self, hq0, hpA]
  have hright (j : ℕ) (hj : A ≤ j) : w j = q (j - A) := by
    exact if_neg (by omega)
  refine ⟨w, (hleft 0 (Nat.zero_le A)).trans hp0, ?_, ?_⟩
  · rw [hright (A + B) (by omega), Nat.add_sub_cancel_left]
    exact hqB
  · intro j hj
    by_cases hjA : j < A
    · rw [hleft j (by omega), hleft (j + 1) (by omega)]
      exact hp j hjA
    · rw [hright j (by omega), hright (j + 1) (by omega)]
      have hidx : j + 1 - A = (j - A) + 1 := by omega
      rw [hidx]
      exact hq (j - A) (by omega)
lemma pad_walk {E : Type*} (R : E → E → Prop)
    {u v : E} {A B : ℕ} (hAB : A ≤ B)
    (w : ℕ → E) (h0 : w 0 = u) (hA : w A = v)
    (hs : ∀ j < A, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ w' : ℕ → E, w' 0 = u ∧ w' B = v ∧
      ∀ j < B, w' j = w' (j + 1) ∨ R (w' j) (w' (j + 1)) := by
  let w' : ℕ → E := fun j => w (min j A)
  refine ⟨w', ?_, ?_, ?_⟩
  · simpa only [w', Nat.zero_min] using h0
  · simpa only [w', Nat.min_eq_right hAB] using hA
  · intro j hj
    by_cases hjA : j < A
    · have h0 : j ≤ A := by omega
      have h1 : j + 1 ≤ A := by omega
      simpa only [w', Nat.min_eq_left h0, Nat.min_eq_left h1] using hs j hjA
    · have h0 : A ≤ j := by omega
      have h1 : A ≤ j + 1 := by omega
      exact Or.inl (by simp only [w', Nat.min_eq_right h0, Nat.min_eq_right h1])

variable {ι : Type*} {E : ι → Type*}
variable [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

end HirschProduct
namespace HirschFaceSplice

lemma extreme_in_extreme_face {d : ℕ}
    {P F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsExtreme ℝ P F)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ P) (hxF : x ∈ F) :
    x ∈ extremePoints ℝ F := by
  refine ⟨hxF, ?_⟩
  intro p hp q hq hopen
  exact hx.2 (hF.1 hp) (hF.1 hq) hopen
lemma face_adj_to_parent {d : ℕ}
    {P F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsExtreme ℝ P F)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : Adj F x y) : Adj P x y :=
  ⟨hxy.1, hF.trans hxy.2⟩
theorem splice_reentry_through_extreme_face
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F)
    (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P)
    (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' (s + B + (L - t)) = v ∧
      ∀ j < s + B + (L - t),
        w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by
  have hsL : s ≤ L := hst.trans htL
  have hsFext : w s ∈ extremePoints ℝ F :=
    extreme_in_extreme_face hF hsP hsF
  have htFext : w t ∈ extremePoints ℝ F :=
    extreme_in_extreme_face hF htP htF

  obtain ⟨wf, hwf0, hwfB, hwfstep⟩ := hFD (w s) hsFext (w t) htFext
  have hwfstepP : ∀ j < B,
      wf j = wf (j + 1) ∨ Adj P (wf j) (wf (j + 1)) := by
    intro j hj
    rcases hwfstep j hj with heq | hadj
    · exact Or.inl heq
    · exact Or.inr (face_adj_to_parent hF hadj)

  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w j
  have hwp0 : wp 0 = u := by simpa [wp] using hw0
  have hwps : wp s = w s := rfl
  have hwpstep : ∀ j < s,
      wp j = wp (j + 1) ∨ Adj P (wp j) (wp (j + 1)) := by
    intro j hj
    simpa [wp] using hwstep j (lt_of_lt_of_le hj hsL)

  let ws : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (t + j)
  have hws0 : ws 0 = w t := by simp [ws]
  have hwsB : ws (L - t) = v := by
    have hidx : t + (L - t) = L := by omega
    simpa [ws, hidx] using hwL
  have hwsstep : ∀ j < L - t,
      ws j = ws (j + 1) ∨ Adj P (ws j) (ws (j + 1)) := by
    intro j hj
    have hidx : t + j < L := by omega
    have h := hwstep (t + j) hidx
    simpa [ws, Nat.add_assoc] using h

  obtain ⟨wpf, hwpf0, hwpfB, hwpfstep⟩ :=
    HirschProduct.append_walk (Adj P) wp wf
      hwp0 hwps hwf0 hwfB hwpstep hwfstepP
  obtain ⟨w', hw'0, hw'B, hw'step⟩ :=
    HirschProduct.append_walk (Adj P) wpf ws
      hwpf0 hwpfB hws0 hwsB hwpfstep hwsstep
  refine ⟨w', hw'0, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hw'B
  · simpa [Nat.add_assoc] using hw'step

end HirschFaceSplice
namespace HirschPolynomialAccess

variable {d : ℕ}
lemma adj_right_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {u z : EuclideanSpace ℝ (Fin d)}
    (hadj : Adj P u z) : z ∈ extremePoints ℝ P := by
  rcases hadj with ⟨huz, hseg⟩
  have hzP : z ∈ P := hseg.subset (right_mem_segment ℝ u z)
  refine ⟨hzP, ?_⟩
  intro x hxP y hyP hzopen
  have hxseg : x ∈ segment ℝ u z :=
    hseg.left_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  have hyseg : y ∈ segment ℝ u z :=
    hseg.right_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hxseg
  obtain ⟨c, e, hc, he, hce, hy⟩ := hyseg
  obtain ⟨s, t, hs, ht, hst, hxy⟩ := hzopen
  have hcoeff : s * a + t * c + (s * b + t * e) = 1 := by
    calc
      s * a + t * c + (s * b + t * e) = s * (a + b) + t * (c + e) := by ring
      _ = s * 1 + t * 1 := by rw [hab, hce]
      _ = 1 := by linarith
  have hlin0 : s • x + t • y - z = 0 := sub_eq_zero.mpr hxy
  rw [← hx, ← hy] at hlin0
  have hrewrite :
      s • (a • u + b • z) + t • (c • u + e • z) - z =
        (s * a + t * c) • u + (s * b + t * e - 1) • z := by
    module
  have hlin1 :
      (s * a + t * c) • u + (s * b + t * e - 1) • z = 0 := by
    rw [← hrewrite]
    exact hlin0
  have hB : s * b + t * e - 1 = -(s * a + t * c) := by
    linarith [hcoeff]
  rw [hB] at hlin1
  have hlin : (s * a + t * c) • (u - z) = 0 := by
    rw [smul_sub, sub_eq_add_neg]
    simpa only [neg_smul] using hlin1
  have hcoef : s * a + t * c = 0 :=
    (smul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr huz)
  have ha0 : a = 0 := by
    nlinarith [mul_nonneg ht.le hc]
  have hb1 : b = 1 := by linarith [hab]
  rw [ha0, zero_smul, zero_add, hb1, one_smul] at hx
  exact hx.symm

end HirschPolynomialAccess
namespace HirschFaceSplice

abbrev Walk {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d)))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w L = v ∧
    ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))
def IsShortestLength {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d)) (L : ℕ) : Prop :=
  ∀ K : ℕ, Walk P K u v → L ≤ K
lemma walk_vertices_extreme {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (h0 : w 0 ∈ extremePoints ℝ P)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∀ j ≤ L, w j ∈ extremePoints ℝ P := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    have hjL : j < L := by omega
    rcases hs j hjL with heq | hadj
    · rw [← heq]
      exact ih (by omega)
    · exact HirschPolynomialAccess.adj_right_extreme P hadj
theorem shortest_face_visit_span_le
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F) (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P) (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    t - s ≤ B := by
  have hw' := splice_reentry_through_extreme_face
    d L B s t P F hF hFD u v w hw0 hwL hs hst htL hsP htP hsF htF
  have hle := hmin (s + B + (L - t)) hw'
  omega
theorem shortest_face_visit_card_le
    (d L B : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F) (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P) :
    ((Finset.range (L + 1)).filter (fun j => w j ∈ F)).card ≤ B + 1 := by
  classical
  let S := (Finset.range (L + 1)).filter (fun j => w j ∈ F)
  change S.card ≤ B + 1
  by_cases hne : S.Nonempty
  · let s := S.min' hne
    have hsS : s ∈ S := Finset.min'_mem S hne
    have hsL : s ≤ L := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hsS).1
      omega
    have hsF : w s ∈ F := (Finset.mem_filter.mp hsS).2
    have hsub : S ⊆ Finset.Icc s (s + B) := by
      intro t ht
      have hst : s ≤ t := Finset.min'_le S t ht
      have htL : t ≤ L := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        omega
      have htF : w t ∈ F := (Finset.mem_filter.mp ht).2
      have hspan := shortest_face_visit_span_le d L B s t P F hF hFD u v
        w hw0 hwL hs hmin hst htL (hverts s hsL) (hverts t htL) hsF htF
      exact Finset.mem_Icc.mpr ⟨hst, by omega⟩
    have hcard : (Finset.Icc s (s + B)).card = B + 1 := by simp [Nat.add_assoc]
    exact (Finset.card_le_card hsub).trans_eq hcard
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hS]
theorem shortest_weighted_face_cover_budget
    {ι : Type*} [Fintype ι]
    (d L q : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B weight : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, 0 < weight i → DiamLE (F i) (B i))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P)
    (hcover : ∀ j ≤ L, q ≤ ∑ i, if w j ∈ F i then weight i else 0) :
    q * (L + 1) ≤ ∑ i, weight i * (B i + 1) := by
  classical
  have hcount :
      (∑ j ∈ Finset.range (L + 1), ∑ i, if w j ∈ F i then weight i else 0) =
      ∑ i, weight i * ((Finset.range (L + 1)).filter (fun j => w j ∈ F i)).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : w j ∈ F i <;> simp [hj]
  calc
    q * (L + 1) = ∑ _j ∈ Finset.range (L + 1), q := by simp [Nat.mul_comm]
    _ ≤ ∑ j ∈ Finset.range (L + 1), ∑ i, if w j ∈ F i then weight i else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcover j (by have := Finset.mem_range.mp hj; omega)
    _ = ∑ i, weight i * ((Finset.range (L + 1)).filter (fun j => w j ∈ F i)).card := hcount
    _ ≤ ∑ i, weight i * (B i + 1) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : weight i = 0
      · simp [hi]
      · apply Nat.mul_le_mul_left
        exact shortest_face_visit_card_le d L (B i) P (F i) (hF i)
          (hFD i (Nat.pos_of_ne_zero hi)) u v w hw0 hwL hs hmin hverts
theorem diamLE_of_weighted_face_cover
    {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B weight : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, 0 < weight i → DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ ∑ i, if x ∈ F i then weight i else 0)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L, Walk P L u v) :
    DiamLE P ((∑ i, weight i * (B i + 1)) / q - 1) := by
  classical
  intro u hu v hv
  have hex : ∃ L, Walk P L u v := hconnect u hu v hv
  let L := Nat.find hex
  obtain ⟨w, hw0, hwL, hs⟩ := Nat.find_spec hex
  have hmin : IsShortestLength P u v L := by
    intro K hK
    exact Nat.find_min' hex hK
  have hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P :=
    walk_vertices_extreme P w (by simpa only [hw0] using hu) hs
  have hbudget := shortest_weighted_face_cover_budget d L q P F B weight
    hF hFD u v w hw0 hwL hs hmin hverts
    (fun j hj => hcover (w j) (hverts j hj))
  have hquot : L + 1 ≤ (∑ i, weight i * (B i + 1)) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    simpa only [Nat.mul_comm] using hbudget
  have hL : L ≤ (∑ i, weight i * (B i + 1)) / q - 1 := by omega
  exact HirschProduct.pad_walk (Adj P) hL w hw0 hwL hs

end HirschFaceSplice
namespace HirschPolynomialAccess

theorem vertex_tight_rows_span_checked
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (y : EuclideanSpace ℝ (Fin d))
    (horth : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    y = 0 := by
  classical
  have hlocal : ∀ i : Fin n, ∃ t : ℝ,
      0 < t ∧ t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [horth i hi, abs_zero, mul_zero, hi, sub_self]
    · have hs : 0 < b i - ⟪a i, x⟫ := sub_pos.mpr (lt_of_le_of_ne (hx.1 i) hi)
      have hd : 0 < |⟪a i, y⟫| + 1 := by positivity
      let t : ℝ := (b i - ⟪a i, x⟫) / (|⟪a i, y⟫| + 1)
      have ht : 0 < t := div_pos hs hd
      have hprod : t * (|⟪a i, y⟫| + 1) = b i - ⟪a i, x⟫ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      exact ⟨t, ht, by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset (Fin n), ∃ t : ℝ,
      0 < t ∧ ∀ i ∈ S, t ≤ e i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨t, ht, hti⟩ := ih
      refine ⟨min (e i) t, lt_min (hepos i) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hti j hjS)
  obtain ⟨t, ht, hte⟩ := huniform Finset.univ
  have hbudget : ∀ i, t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    exact (mul_le_mul_of_nonneg_right (hte i (Finset.mem_univ i))
      (abs_nonneg _)).trans (hebound i)
  have hp : x + t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self ⟪a i, y⟫) ht.le
    rw [inner_add_right, inner_smul_right]
    linarith [hbudget i]
  have hm : x - t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (neg_le_abs ⟪a i, y⟫) ht.le
    rw [mul_neg] at hmul
    rw [inner_sub_right, inner_smul_right]
    linarith [hbudget i]
  have hmid : x ∈ openSegment ℝ (x + t • y) (x - t • y) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num,
      by norm_num, ?_⟩
    module
  have hpeq : x + t • y = x := hx.2 hp hm hmid
  have hty : t • y = 0 := by
    have h := congrArg (fun z => z - x) hpeq
    simpa using h
  exact (smul_eq_zero.mp hty).resolve_left (ne_of_gt ht)

end HirschPolynomialAccess
namespace HirschBalancedFaceCover

variable {d n : ℕ}
def rowSupportingFace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}
lemma rowSupportingFace_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    IsExtreme ℝ (Hpoly a b) (rowSupportingFace a b i) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro p hp q hq z hz hzopen
    refine ⟨hp, ?_⟩
    have hztight : ⟪a i, z⟫ = b i := hz.2
    have hp_le := hp i
    have hq_le := hq i
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
    have hinner : ⟪a i, z⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
      rw [← hzcomb]
      simp [inner_add_right, inner_smul_right]
    by_contra hptight
    have hp_lt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hptight
    have h1 : α * ⟪a i, p⟫ < α * b i :=
      mul_lt_mul_of_pos_left hp_lt hα
    have h2 : β * ⟪a i, q⟫ ≤ β * b i :=
      mul_le_mul_of_nonneg_left hq_le hβ.le
    have hb : α * b i + β * b i = b i := by
      rw [← add_mul, hαβ, one_mul]
    linarith

end HirschBalancedFaceCover
namespace HirschRankFaceCover

theorem tight_rows_outside_subspace_card_ge_codim
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    d - Module.finrank ℝ U ≤
      (Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)).card := by
  classical
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)
  let T : Uᗮ →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun y i => ⟪a i.1, (y : EuclideanSpace ℝ (Fin d))⟫
      map_add' := by
        intro y z
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro c y
        funext i
        simp [inner_smul_right] }
  have hinj : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b x hx
    intro i hi
    by_cases hai : a i ∈ U
    · have hy : ⟪a i, (y : EuclideanSpace ℝ (Fin d))⟫ = 0 :=
        (U.mem_orthogonal _).mp y.2 (a i) hai
      have hz : ⟪a i, (z : EuclideanSpace ℝ (Fin d))⟫ = 0 :=
        (U.mem_orthogonal _).mp z.2 (a i) hai
      rw [inner_sub_right, hy, hz, sub_self]
    · have hiS : i ∈ S := by simp [S, hai, hi]
      have hcoord := congrFun hyz ⟨i, hiS⟩
      change ⟪a i, (y : EuclideanSpace ℝ (Fin d))⟫ =
        ⟪a i, (z : EuclideanSpace ℝ (Fin d))⟫ at hcoord
      rw [inner_sub_right, hcoord, sub_self]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hcod : Module.finrank ℝ (S → ℝ) = S.card := by
    simp [Fintype.card_coe]
  have hdim : Module.finrank ℝ U + Module.finrank ℝ Uᗮ = d := by
    simpa only [finrank_euclideanSpace_fin] using U.finrank_add_finrank_orthogonal
  change d - Module.finrank ℝ U ≤ S.card
  rw [hcod] at hle
  omega
def rowSection {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  F ∩ HirschBalancedFaceCover.rowSupportingFace a b i
lemma rowSection_isExtreme {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (hF : IsExtreme ℝ (Hpoly a b) F)
    (i : Fin n) : IsExtreme ℝ F (rowSection a b F i) := by
  exact (hF.inter (HirschBalancedFaceCover.rowSupportingFace_isExtreme a b i)).mono
    hF.subset inter_subset_left
theorem diamLE_of_rank_increasing_row_bounds {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (hF : IsExtreme ℝ (Hpoly a b) F)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hU : Module.finrank ℝ U < d)
    (B : Fin n → ℕ)
    (hFD : ∀ i, a i ∉ U → DiamLE (rowSection a b F i) (B i))
    (hconnect : ∀ u ∈ extremePoints ℝ F, ∀ v ∈ extremePoints ℝ F,
      ∃ L, HirschFaceSplice.Walk F L u v) :
    DiamLE F
      ((∑ i ∈ Finset.univ.filter (fun i => a i ∉ U), (B i + 1)) /
        (d - Module.finrank ℝ U) - 1) := by
  classical
  let weight : Fin n → ℕ := fun i => if a i ∈ U then 0 else 1
  have hcover : ∀ x ∈ extremePoints ℝ F,
      d - Module.finrank ℝ U ≤
        ∑ i, if x ∈ rowSection a b F i then weight i else 0 := by
    intro x hx
    have hxP : x ∈ extremePoints ℝ (Hpoly a b) :=
      hF.extremePoints_subset_extremePoints hx
    have hcount := tight_rows_outside_subspace_card_ge_codim a b x hxP U
    have heq :
        (∑ i, if x ∈ rowSection a b F i then weight i else 0) =
        (Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hai : a i ∈ U <;> by_cases ht : ⟪a i, x⟫ = b i <;>
        simp [rowSection, HirschBalancedFaceCover.rowSupportingFace, weight,
          hx.1, hxP.1, hai, ht]
    rw [heq]
    exact hcount
  have hbound := HirschFaceSplice.diamLE_of_weighted_face_cover
    d (d - Module.finrank ℝ U) (by omega) F (rowSection a b F) B weight
    (rowSection_isExtreme a b F hF)
    (fun i hi => hFD i (by intro hai; simp [weight, hai] at hi))
    hcover hconnect
  have hcost : (∑ i, weight i * (B i + 1)) =
      ∑ i ∈ Finset.univ.filter (fun i => a i ∉ U), (B i + 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hai : a i ∈ U <;> simp [weight, hai]
  rw [hcost] at hbound
  exact hbound

end HirschRankFaceCover

theorem solution {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (hF : IsExtreme ℝ (Hpoly a b) F)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hU : Module.finrank ℝ U < d)
    (B : Fin n → ℕ)
    (hFD : ∀ i, a i ∉ U →
      DiamLE (F ∩ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) (B i))
    (hconnect : ∀ u ∈ extremePoints ℝ F, ∀ v ∈ extremePoints ℝ F,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj F (w j) (w (j + 1))) :
    DiamLE F
      ((∑ i ∈ Finset.univ.filter (fun i => a i ∉ U), (B i + 1)) /
        (d - Module.finrank ℝ U) - 1) := by
  exact HirschRankFaceCover.diamLE_of_rank_increasing_row_bounds a b F hF U hU B hFD hconnect

#print axioms solution
