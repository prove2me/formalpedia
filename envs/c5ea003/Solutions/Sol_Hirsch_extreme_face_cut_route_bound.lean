-- Prove2me | solution 1 for Hirsch.extreme_face_cut_route_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-09T14:02:45.447337+00:00
-- url     : https://prove2.me/submissions/f363f391-d8e3-4357-991f-df321f987aa6

import Definitions.Def_Hirsch_model
import Mathlib

-- BEGIN Solutions/PolynomialProductWalk.lean

open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschProduct

/-- Concatenate padded walks. This is independent of polytope geometry. -/
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

/-- Moving one coordinate along a factor edge, with all other coordinates
fixed at factor vertices, gives a genuine edge of the Cartesian product. -/
lemma update_adj [DecidableEq ι]
    (P : ∀ i, Set (E i)) (base : ∀ i, E i) (i : ι)
    (hfix : ∀ j, j ≠ i → base j ∈ extremePoints ℝ (P j))
    {p q : E i} (hadj : Adj (P i) p q) :
    Adj (Set.univ.pi P) (Function.update base i p) (Function.update base i q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    apply hadj.1
    simpa using congrFun heq i
  · intro z hz
    rw [← Pi.image_update_segment] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.mem_univ_pi]
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hadj.2.subset ht
    · simpa [Function.update_of_ne hji] using (hfix j hji).1
  · intro x hx y hy z hz hopen
    rw [Set.mem_univ_pi] at hx hy
    rw [← Pi.image_update_segment] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hopen
    have hop (j : ι) : Function.update base i t j ∈ openSegment ℝ (x j) (y j) :=
      ⟨α, β, hα, hβ, hαβ, congrFun hcomb j⟩
    have hti : t ∈ openSegment ℝ (x i) (y i) := by simpa using hop i
    have hxi : x i ∈ segment ℝ p q :=
      hadj.2.left_mem_of_mem_openSegment (hx i) (hy i) ht hti
    have hxfix (j : ι) (hji : j ≠ i) : x j = base j :=
      (hfix j hji).2 (hx j) (hy j) (by simpa [Function.update_of_ne hji] using hop j)
    rw [← Pi.image_update_segment]
    refine ⟨x i, hxi, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne hji] using (hxfix j hji).symm

/-- A finite product has a diameter budget equal to the SUM of factor budgets.
The sum, rather than the total dimension, is the relevant routing quantity. -/
theorem diamLE_pi [Fintype ι]
    (P : ∀ i, Set (E i)) (B : ι → ℕ)
    (hD : ∀ i, DiamLE (P i) (B i)) :
    DiamLE (Set.univ.pi P) (∑ i, B i) := by
  classical
  have hwalk : ∀ s : Finset ι, ∀ u v : ∀ i, E i,
      (∀ i, u i ∈ extremePoints ℝ (P i)) →
      (∀ i, v i ∈ extremePoints ℝ (P i)) →
      (∀ i, i ∉ s → u i = v i) →
      ∃ w : ℕ → (∀ i, E i), w 0 = u ∧ w (∑ i ∈ s, B i) = v ∧
        ∀ j < ∑ i ∈ s, B i,
          w j = w (j + 1) ∨ Adj (Set.univ.pi P) (w j) (w (j + 1)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro u v hu hv heq
        have huv : u = v := funext (fun i => heq i (by simp))
        subst v
        exact ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
    | @insert i s his ih =>
        intro u v hu hv heq
        let mid : ∀ j, E j := Function.update u i (v i)
        have hm (j : ι) : mid j ∈ extremePoints ℝ (P j) := by
          by_cases hji : j = i
          · subst j
            simpa [mid] using hv i
          · simpa [mid, Function.update_of_ne hji] using hu j
        have hsame (j : ι) (hjs : j ∉ s) : mid j = v j := by
          by_cases hji : j = i
          · subst j
            simp [mid]
          · simpa [mid, Function.update_of_ne hji] using heq j (by simp [hji, hjs])
        obtain ⟨q, hq0, hqB, hqstep⟩ := ih mid v hm hv hsame
        obtain ⟨p, hp0, hpB, hpstep⟩ := hD i (u i) (hu i) (v i) (hv i)
        let wp : ℕ → (∀ j, E j) := fun t => Function.update u i (p t)
        have hwp0 : wp 0 = u := by simp [wp, hp0]
        have hwpB : wp (B i) = mid := by simp [wp, hpB, mid]
        have hwps : ∀ j < B i, wp j = wp (j + 1) ∨
            Adj (Set.univ.pi P) (wp j) (wp (j + 1)) := by
          intro j hj
          rcases hpstep j hj with h | h
          · exact Or.inl (congrArg (Function.update u i) h)
          · exact Or.inr (update_adj P u i (fun k _ => hu k) h)
        obtain ⟨w, hw0, hwB, hwstep⟩ :=
          append_walk (Adj (Set.univ.pi P)) wp q hwp0 hwpB hq0 hqB hwps hqstep
        refine ⟨w, hw0, ?_, ?_⟩
        · simpa only [Finset.sum_insert his] using hwB
        · simpa only [Finset.sum_insert his] using hwstep
  intro u hu v hv
  have hu' : ∀ i, u i ∈ extremePoints ℝ (P i) := by
    simpa only [extremePoints_pi, Set.mem_univ_pi] using hu
  have hv' : ∀ i, v i ∈ extremePoints ℝ (P i) := by
    simpa only [extremePoints_pi, Set.mem_univ_pi] using hv
  exact hwalk Finset.univ u v hu' hv' (fun i hi => False.elim (hi (Finset.mem_univ i)))


end HirschProduct
end


-- BEGIN Solutions/PolynomialFaceReentrySplice.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschFaceSplice

/-- A parent extreme point lying in an extreme face is also extreme in that
face. -/
lemma extreme_in_extreme_face {d : ℕ}
    {P F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsExtreme ℝ P F)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ P) (hxF : x ∈ F) :
    x ∈ extremePoints ℝ F := by
  refine ⟨hxF, ?_⟩
  intro p hp q hq hopen
  exact hx.2 (hF.1 hp) (hF.1 hq) hopen

/-- Every edge of an extreme face is an edge of the parent polytope. -/
lemma face_adj_to_parent {d : ℕ}
    {P F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsExtreme ℝ P F)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : Adj F x y) : Adj P x y :=
  ⟨hxy.1, hF.trans hxy.2⟩

/-- Replace an arbitrary segment between two visits to an extreme face by a
shortest padded walk inside that face.

If a parent path of length `L` visits `F` at indices `s ≤ t`, and `F` has
face-diameter budget `B`, the repaired parent path has exact budget

` s + B + (L - t) `.

Crucially this depends only on the first/last selected visits, not on how many
times the original path left and re-entered `F` between them. -/
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

/-- If the face diameter is no larger than the span of the segment being
replaced, re-entry can be eliminated without increasing the original path
budget. -/
theorem splice_reentry_no_growth
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
    (hsF : w s ∈ F) (htF : w t ∈ F)
    (hB : B ≤ t - s) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' L = v ∧
      ∀ j < L, w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by
  obtain ⟨w0, h0, hK, hs⟩ :=
    splice_reentry_through_extreme_face
      d L B s t P F hF hFD u v w hw0 hwL hwstep
      hst htL hsP htP hsF htF
  have hKL : s + B + (L - t) ≤ L := by omega
  exact HirschProduct.pad_walk (Adj P) hKL w0 h0 hK hs

/-- Without any span comparison, all re-entry through one fixed face costs at
most one copy of that face's diameter budget. -/
theorem splice_reentry_cost_at_most_face_diameter
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
      w' 0 = u ∧ w' (L + B) = v ∧
      ∀ j < L + B,
        w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by
  obtain ⟨w0, h0, hK, hs⟩ :=
    splice_reentry_through_extreme_face
      d L B s t P F hF hFD u v w hw0 hwL hwstep
      hst htL hsP htP hsF htF
  have hKL : s + B + (L - t) ≤ L + B := by omega
  exact HirschProduct.pad_walk (Adj P) hKL w0 h0 hK hs


end HirschFaceSplice
end


-- BEGIN Solutions/PolynomialRegionRouting.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A padded route using only the supplied relation. -/
def Route {V : Type*} (R : V → V → Prop) (B : ℕ) (u v : V) : Prop :=
  ∃ w : ℕ → V, w 0 = u ∧ w B = v ∧
    ∀ j < B, w j = w (j + 1) ∨ R (w j) (w (j + 1))

/-- Region intersections, not overlap of intervals in an old sequence. -/
def intersectionGraph {V ι : Type*} (S : ι → Set V) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ∃ z, z ∈ S i ∧ z ∈ S j
  symm := by
    intro i j h
    obtain ⟨hne, z, hi, hj⟩ := h
    exact ⟨hne.symm, z, hj, hi⟩
  loopless := ⟨fun i h => h.1 rfl⟩

lemma shared_point_walk {V ι : Type*} (S : ι → Set V)
    {i j : ι} {z : V} (hi : z ∈ S i) (hj : z ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  classical
  by_cases hij : i = j
  · subst j
    exact ⟨.nil⟩
  · exact ⟨.cons ⟨hij, z, hi, hj⟩ .nil⟩

/-- Traverse a walk of regions, paying the cost of each region occurrence. -/
theorem route_of_region_walk {V ι : Type*}
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    {i j : ι} (p : (intersectionGraph S).Walk i j) :
    ∀ u ∈ S i, ∀ v ∈ S j, Route R ((p.support.map C).sum) u v := by
  induction p with
  | @nil i =>
      intro u hu v hv
      simpa using hlocal i u hu v hv
  | @cons i k j hik p ih =>
      intro u hu v hv
      obtain ⟨z, hzi, hzk⟩ := hik.2
      obtain ⟨a, ha0, haC, has⟩ := hlocal i u hu z hzi
      obtain ⟨b, hb0, hbC, hbs⟩ := ih z hzk v hv
      obtain ⟨q, hq0, hqC, hqs⟩ :=
        HirschProduct.append_walk R a b ha0 haC hb0 hbC has hbs
      exact ⟨q, hq0, hqC, hqs⟩

/-- A list without repeated labels charges each available region at most once. -/
lemma nodup_cost_le {ι : Type*} (C : ι → ℕ) (l : List ι)
    (s : Finset ι) (hnd : l.Nodup) (hsub : ∀ i ∈ l, i ∈ s) :
    (l.map C).sum ≤ ∑ i ∈ s, C i := by
  classical
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
      have hp := List.nodup_cons.mp hnd
      have ha : a ∈ s := hsub a (by simp)
      have htail : ∀ i ∈ l, i ∈ s.erase a := by
        intro i hi
        apply Finset.mem_erase.mpr
        refine ⟨?_, hsub i (by simp [hi])⟩
        intro hia
        subst i
        exact hp.1 hi
      have ht := ih (s.erase a) hp.2 htail
      have heq := Finset.add_sum_erase s C ha
      simpa only [List.map_cons, List.sum_cons] using
        (Nat.add_le_add_left ht (C a)).trans_eq heq

/-- Erasing repeated region labels gives a one-charge-per-region bound.
No order or laminarity assumption is made about appearances in an old walk. -/
theorem route_of_connected_regions {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    {i j : ι} (hreach : Nonempty ((intersectionGraph S).Walk i j))
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    Route R (∑ k, C k) u v := by
  classical
  obtain ⟨walk⟩ := hreach
  let p := walk.toPath
  have hnd : p.val.support.Nodup := p.property.support_nodup
  have hle := nodup_cost_le C p.val.support Finset.univ hnd (by simp)
  obtain ⟨q, hq0, hqB, hqstep⟩ := route_of_region_walk R S C hlocal p.val u hu v hv
  exact HirschProduct.pad_walk R hle q hq0 hqB hqstep

/-- If every consecutive pair is covered by a region, endpoint region labels
are connected even when regions are revisited in an arbitrary order. -/
lemma region_walk_of_step_cover {V ι : Type*}
    (S : ι → Set V) (w : ℕ → V) (L : ℕ)
    (hcover : ∀ k < L, ∃ i, w k ∈ S i ∧ w (k + 1) ∈ S i)
    (i j : ι) (hi : w 0 ∈ S i) (hj : w L ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  induction L generalizing j with
  | zero => exact shared_point_walk S hi hj
  | succ L ih =>
      obtain ⟨k, hkL, hkNext⟩ := hcover L (Nat.lt_succ_self L)
      obtain ⟨p⟩ := ih (fun a ha => hcover a (Nat.lt_succ_of_lt ha)) k hkL
      obtain ⟨q⟩ := shared_point_walk S hkNext hj
      exact ⟨p.append q⟩

/-- Compress arbitrarily many covered transitions into a route whose budget
is the sum over distinct available regions, not the sum over occurrences. -/
theorem route_of_step_cover {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (w : ℕ → V) (L : ℕ)
    (hcover : ∀ k < L, ∃ i, w k ∈ S i ∧ w (k + 1) ∈ S i) :
    Route R (∑ i, C i) (w 0) (w L) := by
  by_cases hL : L = 0
  · subst L
    exact ⟨fun _ => w 0, rfl, rfl, fun _ _ => Or.inl rfl⟩
  · have hpos : 0 < L := Nat.pos_of_ne_zero hL
    obtain ⟨i, hi, _⟩ := hcover 0 hpos
    obtain ⟨j, _, hj⟩ := hcover (L - 1) (by omega)
    have hj' : w L ∈ S j := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ L)] using hj
    exact route_of_connected_regions R S C hlocal
      (region_walk_of_step_cover S w L hcover i j hi hj') (w 0) (w L) hi hj'

/-- An extreme face supplies a routing region on the parent's extreme vertices. -/
lemma extreme_face_region {d : ℕ}
    (P F : Set (EuclideanSpace ℝ (Fin d))) (B : ℕ)
    (hF : IsExtreme ℝ P F) (hD : DiamLE F B) :
    ∀ u ∈ extremePoints ℝ P ∩ F, ∀ v ∈ extremePoints ℝ P ∩ F,
      Route (Adj P) B u v := by
  intro u hu v hv
  obtain ⟨q, hq0, hqB, hs⟩ := hD u
    (HirschFaceSplice.extreme_in_extreme_face hF hu.1 hu.2) v
    (HirschFaceSplice.extreme_in_extreme_face hF hv.1 hv.2)
  refine ⟨q, hq0, hqB, ?_⟩
  intro k hk
  rcases hs k hk with heq | hadj
  · exact Or.inl heq
  · exact Or.inr (HirschFaceSplice.face_adj_to_parent hF hadj)

/-- Face-covered transitions can be arbitrarily interleaved. Repeated visits
to the same face do not multiply its cost, provided every transition is
certified by an actual common face of its two parent vertices. -/
theorem route_of_face_covered_sequence {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_step_cover (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i)) w L
  intro k hk
  obtain ⟨i, hi, hi'⟩ := hcover k hk
  exact ⟨i, ⟨hverts k (by omega), hi⟩, ⟨hverts (k + 1) (by omega), hi'⟩⟩


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialMixedRegionRouting.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

lemma route_one {V : Type*} (R : V → V → Prop) {u v : V}
    (h : u = v ∨ R u v) : Route R 1 u v := by
  refine ⟨fun k => if k = 0 then u else v, by simp, by simp, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa using h

lemma pair_region {V : Type*} (R : V → V → Prop) (a b : V)
    (hab : R a b) (hba : R b a) :
    ∀ u ∈ ({a, b} : Set V), ∀ v ∈ ({a, b} : Set V), Route R 1 u v := by
  intro u hu v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact route_one R (Or.inl rfl)
  · exact route_one R (Or.inr hab)
  · exact route_one R (Or.inr hba)
  · exact route_one R (Or.inl rfl)

/-- Repeated uses of the same repair region or surviving bridge do not
multiply its charge. Chronological crossing of region visits is allowed. -/
theorem route_of_mixed_step_cover {V ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (a b : κ → V) (hab : ∀ k, R (a k) (b k)) (hba : ∀ k, R (b k) (a k))
    (w : ℕ → V) (L : ℕ)
    (hcover : ∀ k < L,
      (∃ i, w k ∈ S i ∧ w (k + 1) ∈ S i) ∨
      (∃ e, w k ∈ ({a e, b e} : Set V) ∧ w (k + 1) ∈ ({a e, b e} : Set V))) :
    Route R ((∑ i, C i) + Fintype.card κ) (w 0) (w L) := by
  let T : Sum ι κ → Set V := Sum.elim S (fun e => {a e, b e})
  let D : Sum ι κ → ℕ := Sum.elim C (fun _ => 1)
  have hlocalT : ∀ i, ∀ u ∈ T i, ∀ v ∈ T i, Route R (D i) u v := by
    intro i
    cases i with
    | inl i => exact hlocal i
    | inr e => exact pair_region R (a e) (b e) (hab e) (hba e)
  have hcoverT : ∀ k < L, ∃ i, w k ∈ T i ∧ w (k + 1) ∈ T i := by
    intro k hk
    rcases hcover k hk with ⟨i, hi, hi'⟩ | ⟨e, he, he'⟩
    · exact ⟨Sum.inl i, hi, hi'⟩
    · exact ⟨Sum.inr e, he, he'⟩
  have h := route_of_step_cover R T D hlocalT w L hcoverT
  simpa [D, Fintype.sum_sum_type] using h

/-- Unordered face-damage amortization in the parent vertex graph.
The input need not be a valid graph walk. Each consecutive pair must instead
lie in one certified extreme face or on one listed surviving edge. The output
pays each available face once plus one for each listed surviving edge. -/
theorem route_of_faces_and_surviving_edges
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (a b : κ → EuclideanSpace ℝ (Fin d)) (hedge : ∀ e, Adj P (a e) (b e))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ P)
    (hcover : ∀ k < L,
      (∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) ∨
      (∃ e, w k ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))) ∧
        w (k + 1) ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))))) :
    Route (Adj P) ((∑ i, B i) + Fintype.card κ) (w 0) (w L) := by
  have hrev : ∀ e, Adj P (b e) (a e) := by
    intro e
    refine ⟨(hedge e).1.symm, ?_⟩
    rw [segment_symm]
    exact (hedge e).2
  apply route_of_mixed_step_cover (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i)) a b hedge hrev w L
  intro k hk
  rcases hcover k hk with ⟨i, hi, hi'⟩ | hgood
  · exact Or.inl ⟨i, ⟨hverts k (by omega), hi⟩,
      ⟨hverts (k + 1) (by omega), hi'⟩⟩
  · exact Or.inr hgood


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialRepairNetworkCuts.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- Every partition of the region labels separating the endpoint labels
has a genuine shared point across it. No chronological overlap is used. -/
def RegionCutCondition {V ι : Type*} (S : ι → Set V) (i j : ι) : Prop :=
  ∀ A : Set ι, i ∈ A → j ∉ A →
    ∃ a ∈ A, ∃ b, b ∉ A ∧ ∃ z, z ∈ S a ∧ z ∈ S b

/-- A reachable region cannot be separated from the start by disjoint regions. -/
lemma region_cut_condition_of_walk {V ι : Type*} (S : ι → Set V)
    {i j : ι} (p : (intersectionGraph S).Walk i j) :
    RegionCutCondition S i j := by
  classical
  induction p with
  | @nil i =>
      intro A hi hj
      exact (hj hi).elim
  | @cons i k j hik p ih =>
      intro A hi hj
      by_cases hk : k ∈ A
      · exact ih A hk hj
      · exact ⟨i, hi, k, hk, hik.2⟩

/-- The reachable-label set supplies a separating cut whenever no region
walk exists. This is an exact certificate criterion, not parent connectivity. -/
theorem region_walk_iff_cut_condition {V ι : Type*} (S : ι → Set V)
    (i j : ι) :
    Nonempty ((intersectionGraph S).Walk i j) ↔ RegionCutCondition S i j := by
  classical
  constructor
  · rintro ⟨p⟩
    exact region_cut_condition_of_walk S p
  · intro hcut
    by_contra hno
    let A : Set ι := {k | Nonempty ((intersectionGraph S).Walk i k)}
    have hi : i ∈ A := ⟨.nil⟩
    have hj : j ∉ A := hno
    obtain ⟨a, ha, b, hb, z, hza, hzb⟩ := hcut A hi hj
    obtain ⟨p⟩ := ha
    obtain ⟨q⟩ := shared_point_walk S hza hzb
    exact hb ⟨p.append q⟩

/-- A finite repair network pays each available region once, provided every
separating label cut has an actual shared-point bridge. -/
theorem route_of_region_cut_condition {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ k, ∀ x ∈ S k, ∀ y ∈ S k, Route R (C k) x y)
    (i j : ι) (hcut : RegionCutCondition S i j)
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    Route R (∑ k, C k) u v := by
  exact route_of_connected_regions R S C hlocal
    ((region_walk_iff_cut_condition S i j).mpr hcut) u v hu hv

/-- A selected finite subfamily is enough; unused regions incur no charge.
The ambient label type need not itself be finite. -/
theorem route_of_subfamily_cut_condition {V ι : Type*}
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ) (K : Finset ι)
    (hlocal : ∀ k ∈ K, ∀ x ∈ S k, ∀ y ∈ S k, Route R (C k) x y)
    (i j : K)
    (hcut : RegionCutCondition (fun k : K => S k) i j)
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    Route R (∑ k : K, C k) u v := by
  exact route_of_region_cut_condition R (fun k : K => S k) (fun k : K => C k)
    (fun k => hlocal k k.property) i j hcut u v hu hv

/-- Failure of certificate connectivity has a concrete separating cut.
It does not imply that the full parent relation has no route. -/
theorem route_or_separating_region_cut {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ k, ∀ x ∈ S k, ∀ y ∈ S k, Route R (C k) x y)
    (i j : ι) (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    Route R (∑ k, C k) u v ∨
      ∃ A : Set ι, i ∈ A ∧ j ∉ A ∧
        ∀ a ∈ A, ∀ b, b ∉ A → ∀ z, z ∈ S a → z ∉ S b := by
  classical
  by_cases hreach : Nonempty ((intersectionGraph S).Walk i j)
  · exact Or.inl (route_of_connected_regions R S C hlocal hreach u v hu hv)
  · right
    let A : Set ι := {k | Nonempty ((intersectionGraph S).Walk i k)}
    refine ⟨A, ⟨.nil⟩, hreach, ?_⟩
    intro a ha b hb z hza hzb
    obtain ⟨p⟩ := ha
    obtain ⟨q⟩ := shared_point_walk S hza hzb
    exact hb ⟨p.append q⟩

/-- In a polyhedral application, cuts must be bridged by actual parent
vertices lying in both faces, not merely by overlapping time intervals. -/
theorem route_of_extreme_face_cut_condition {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ k, IsExtreme ℝ P (F k)) (hD : ∀ k, DiamLE (F k) (B k))
    (i j : ι)
    (hcut : RegionCutCondition (fun k => extremePoints ℝ P ∩ F k) i j)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ P ∩ F i)
    (hv : v ∈ extremePoints ℝ P ∩ F j) :
    Route (Adj P) (∑ k, B k) u v := by
  exact route_of_region_cut_condition (Adj P) (fun k => extremePoints ℝ P ∩ F k) B
    (fun k => extreme_face_region P (F k) (B k) (hF k) (hD k)) i j hcut u v hu hv

/-- A one-sided integer potential supplies an independently checkable route
lower bound, including equality padding steps. -/
theorem potential_le_of_route {V : Type*} (R : V → V → Prop) (φ : V → ℕ)
    (hφ : ∀ x y, R x y → φ y ≤ φ x + 1)
    {B : ℕ} {u v : V} (hroute : Route R B u v) : φ v ≤ φ u + B := by
  obtain ⟨w, hw0, hwB, hs⟩ := hroute
  have hp : ∀ k, k ≤ B → φ (w k) ≤ φ u + k := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [hw0]
    | succ k ih =>
        intro hk
        have hi := ih (by omega)
        rcases hs k (by omega) with heq | hadj
        · rw [← heq]
          omega
        · have hstep := hφ (w k) (w (k + 1)) hadj
          omega
  simpa [hwB] using hp B (Nat.le_refl B)


end HirschRegionRoute
end


-- BEGIN Solutions/Sol_Hirsch_extreme_face_cut_route_bound.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public wrapper for the polyhedral repair-network cut theorem, with the
local Route and RegionCutCondition vocabulary expanded from its type. -/
theorem solution {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ k, IsExtreme ℝ P (F k)) (hD : ∀ k, DiamLE (F k) (B k))
    (i j : ι)
    (hcut : ∀ A : Set ι, i ∈ A → j ∉ A →
      ∃ a ∈ A, ∃ b, b ∉ A ∧ ∃ z,
        z ∈ extremePoints ℝ P ∧ z ∈ F a ∧ z ∈ F b)
    (u v : EuclideanSpace ℝ (Fin d))
    (huP : u ∈ extremePoints ℝ P) (huF : u ∈ F i)
    (hvP : v ∈ extremePoints ℝ P) (hvF : v ∈ F j) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (∑ k, B k) = v ∧
      ∀ r < ∑ k, B k, q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by
  have hc : HirschRegionRoute.RegionCutCondition
      (fun k => extremePoints ℝ P ∩ F k) i j := by
    intro A hi hj
    obtain ⟨a, ha, b, hb, z, hzP, hza, hzb⟩ := hcut A hi hj
    exact ⟨a, ha, b, hb, z, ⟨hzP, hza⟩, ⟨hzP, hzb⟩⟩
  exact HirschRegionRoute.route_of_extreme_face_cut_condition
    P F B hF hD i j hc u v ⟨huP, huF⟩ ⟨hvP, hvF⟩

end


#print axioms solution
