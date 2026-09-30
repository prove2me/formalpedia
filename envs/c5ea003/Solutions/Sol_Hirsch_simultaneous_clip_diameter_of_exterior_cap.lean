-- Prove2me | solution 1 for Hirsch.simultaneous_clip_diameter_of_exterior_cap
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T01:47:55.774527+00:00
-- url     : https://prove2.me/submissions/9e7561b5-4ca6-4e2f-acf5-d9f87f7b9d91

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


-- BEGIN Solutions/PolynomialIntervalRegionRouting.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A chronological interval cover connects its endpoint regions when every
closed interval overlap is backed by an actual shared point of the regions.
Interior entries of the old sequence are not used as portals. -/
lemma region_walk_of_interval_cover {V ι : Type*}
    (S : ι → Set V) (s t : ι → ℕ)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j)
    (L : ℕ)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (i j : ι) (hi : s i ≤ 0 ∧ 0 ≤ t i)
    (hj : s j ≤ L ∧ L ≤ t j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  induction L generalizing j with
  | zero =>
      obtain ⟨z, hzi, hzj⟩ := hportal i j
        (hi.1.trans hj.2) (hj.1.trans hi.2)
      exact shared_point_walk S hzi hzj
  | succ L ih =>
      obtain ⟨k, hks, hkt⟩ := hcover L (Nat.lt_succ_self L)
      obtain ⟨p⟩ := ih (fun a ha => hcover a (Nat.lt_succ_of_lt ha)) k
        ⟨hks, (Nat.le_succ L).trans hkt⟩
      obtain ⟨z, hzk, hzj⟩ := hportal k j
        (hks.trans ((Nat.le_succ L).trans hj.2)) (hj.1.trans hkt)
      obtain ⟨q⟩ := shared_point_walk S hzk hzj
      exact ⟨p.append q⟩

/-- Unordered endpoint-supported interval repair. The sequence may have invalid
steps and arbitrary interior points. It is enough that intervals cover every
step, each interval's endpoints lie in its routing region, and chronological
overlaps have genuine region portals. Every available region is charged once.

This does not infer geometric intersection from temporal overlap: `hportal`
is the separate geometric hypothesis which makes crossing intervals safe. -/
theorem route_of_interval_cover {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (s t : ι → ℕ) (w : ℕ → V) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hends : ∀ i, w (s i) ∈ S i ∧ w (t i) ∈ S i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j) :
    Route R (∑ i, C i) (w 0) (w L) := by
  by_cases hL : L = 0
  · subst L
    exact ⟨fun _ => w 0, rfl, rfl, fun _ _ => Or.inl rfl⟩
  · have hpos : 0 < L := Nat.pos_of_ne_zero hL
    obtain ⟨i, hsi, hti⟩ := hcover 0 hpos
    have hsi0 : s i = 0 := Nat.eq_zero_of_le_zero hsi
    obtain ⟨j, hsj, htj⟩ := hcover (L - 1) (by omega)
    have hlast : L - 1 + 1 = L := Nat.sub_add_cancel (by omega : 1 ≤ L)
    rw [hlast] at htj
    have htjL : t j = L := Nat.le_antisymm (hbound j) htj
    have hi : w 0 ∈ S i := by simpa only [hsi0] using (hends i).1
    have hj : w L ∈ S j := by simpa only [htjL] using (hends j).2
    have hreach := region_walk_of_interval_cover S s t hportal L hcover i j
      ⟨hsi, Nat.zero_le _⟩ ⟨hsj.trans (Nat.sub_le _ _), htj⟩
    exact route_of_connected_regions R S C hlocal hreach (w 0) (w L) hi hj

/-- Geometric specialization: a shared parent extreme vertex is a valid portal
between two extreme-face repairs. Only marked interval endpoints must remain
parent vertices; the old sequence's interior entries need not remain feasible.
The conclusion is conditional on the stated portal and face-diameter data. -/
theorem route_of_face_interval_cover {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ extremePoints ℝ P ∧ z ∈ F i ∧ z ∈ F j) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_interval_cover (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i)) s t w L hbound
  · intro i
    exact ⟨⟨(hverts i).1, (hends i).1⟩, ⟨(hverts i).2, (hends i).2⟩⟩
  · exact hcover
  · intro i j hij hji
    obtain ⟨z, hz, hzi, hzj⟩ := hportal i j hij hji
    exact ⟨z, ⟨hz, hzi⟩, ⟨hz, hzj⟩⟩


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialIntervalStartPortals.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- Chronological overlap has an automatic region portal when every interval
contains the start point of every later interval that begins before it ends.
The later start itself is the shared point. -/
lemma interval_portal_of_start_containment {V ι : Type*}
    (S : ι → Set V) (s t : ι → ℕ) (w : ℕ → V)
    (hstart : ∀ j, w (s j) ∈ S j)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ S i) :
    ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j := by
  intro i j hij hji
  by_cases hs : s i ≤ s j
  · exact ⟨w (s j), hcontain i j hs hji, hstart j⟩
  · have hjs : s j ≤ s i := Nat.le_of_not_ge hs
    exact ⟨w (s i), hstart i, hcontain j i hjs hij⟩

/-- Generic interval routing with no separate existential portal hypothesis:
start-containment implies the portal condition required by `route_of_interval_cover`. -/
theorem route_of_interval_cover_of_start_containment
    {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (s t : ι → ℕ) (w : ℕ → V) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hends : ∀ i, w (s i) ∈ S i ∧ w (t i) ∈ S i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ S i) :
    Route R (∑ i, C i) (w 0) (w L) := by
  apply route_of_interval_cover R S C hlocal s t w L hbound hends hcover
  exact interval_portal_of_start_containment S s t w (fun j => (hends j).1) hcontain

/-- Extreme-face specialization.  It is enough that each interval's start and
end are parent vertices in its own face, and that a later interval start which
occurs before an earlier interval ends lies in the earlier supporting face.
The later start is then a genuine parent-vertex portal between the two faces. -/
theorem route_of_face_interval_cover_of_start_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover P F B hF hD s t w L hbound hverts hends hcover
  intro i j hij hji
  by_cases hs : s i ≤ s j
  · exact ⟨w (s j), (hverts j).1, hcontain i j hs hji, (hends j).1⟩
  · have hjs : s j ≤ s i := Nat.le_of_not_ge hs
    exact ⟨w (s i), (hverts i).1, (hends i).1, hcontain j i hjs hij⟩

/-- More geometric but stronger sufficient hypothesis: if every checkpoint of
an interval remains in its supporting face throughout that valid interval,
then start-containment is automatic and the same total face-budget route
follows. This is the form closest to a Case-VII statement that a damaged path
segment lies in one common face. -/
theorem route_of_face_interval_cover_of_active_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hvalid : ∀ i, s i ≤ t i)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover_of_start_containment
    P F B hF hD s t w L hbound hverts
    (fun i => ⟨hactive i (s i) (Nat.le_refl _) (hvalid i),
      hactive i (t i) (hvalid i) (Nat.le_refl _)⟩)
    hcover
  intro i j hs hst
  exact hactive i (s j) hs hst


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialFacePreservingCheckpoints.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A nonempty closed extreme subset of a compact parent contains a parent
extreme vertex. The given point need not itself be a vertex. -/
theorem compact_face_point_has_parent_vertex
    {d : ℕ} (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hclosed : IsClosed F)
    (hne : F.Nonempty) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F := by
  obtain ⟨v, hv⟩ :=
    (hP.of_isClosed_subset hclosed hF.subset).extremePoints_nonempty hne
  exact ⟨v, hF.extremePoints_subset_extremePoints hv, hv.1⟩

/-- All closed parent extreme faces containing a feasible point can be
preserved simultaneously by one parent vertex. No finiteness assumption on
the face family is necessary. This is an incidence selector, not a continuous
map, a nearest-vertex map, or a claim that a circuit step is an edge. -/
theorem exists_vertex_preserving_face_memberships
    {d : ℕ} {ι : Type*} (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ P) :
    ∃ v, v ∈ extremePoints ℝ P ∧ ∀ i, x ∈ F i → v ∈ F i := by
  let G : Set (EuclideanSpace ℝ (Fin d)) :=
    P ∩ ⋂ i, ⋂ (_ : x ∈ F i), F i
  have hGc : IsClosed G :=
    hP.isClosed.inter (isClosed_iInter fun i => isClosed_iInter fun _ => hclosed i)
  have hxG : x ∈ G :=
    ⟨hx, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => hi⟩
  have hGe : IsExtreme ℝ P G := by
    refine ⟨fun _ hz => hz.1, ?_⟩
    intro a ha b hb z hz hseg
    refine ⟨ha, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => ?_⟩
    exact (hF i).left_mem_of_mem_openSegment ha hb
      (mem_iInter.mp (mem_iInter.mp hz.2 i) hi) hseg
  obtain ⟨v, hv, hvG⟩ := compact_face_point_has_parent_vertex P G hP hGe hGc ⟨x, hxG⟩
  exact ⟨v, hv, fun i hi => mem_iInter.mp (mem_iInter.mp hvG.2 i) hi⟩

/-- A single face-membership-preserving vertex selection fixes every parent
vertex. It may be discontinuous and need not preserve adjacency. -/
theorem face_preserving_vertex_selection
    {d : ℕ} {ι : Type*} (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) :
    ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x ∈ P, r x ∈ extremePoints ℝ P) ∧
      (∀ x ∈ extremePoints ℝ P, r x = x) ∧
      (∀ i x, x ∈ F i → r x ∈ F i) := by
  classical
  have hchoice : ∀ x : EuclideanSpace ℝ (Fin d), ∃ v,
      (x ∈ P → v ∈ extremePoints ℝ P) ∧
      (x ∈ extremePoints ℝ P → v = x) ∧
      (∀ i, x ∈ F i → v ∈ F i) := by
    intro x
    by_cases hxv : x ∈ extremePoints ℝ P
    · exact ⟨x, fun _ => hxv, fun _ => rfl, fun _ hi => hi⟩
    · by_cases hx : x ∈ P
      · obtain ⟨v, hv, hmem⟩ :=
          exists_vertex_preserving_face_memberships P F hP hF hclosed x hx
        exact ⟨v, fun _ => hv, fun h => False.elim (hxv h), hmem⟩
      · exact ⟨x, fun h => False.elim (hx h), fun _ => rfl, fun _ hi => hi⟩
  choose r hr using hchoice
  exact ⟨r, fun x hx => (hr x).1 hx, fun x hx => (hr x).2.1 hx,
    fun i x hx => (hr x).2.2 i hx⟩

/-- Geometric overlap of closed faces of a compact parent supplies a genuine
parent-vertex portal, even when the overlap witness is nonvertex. -/
theorem compact_faces_shared_point_portal
    {d : ℕ} (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (x : EuclideanSpace ℝ (Fin d)) (hxF : x ∈ F) (hxG : x ∈ G) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G := by
  obtain ⟨v, hv, hvFG⟩ := compact_face_point_has_parent_vertex
    P (F ∩ G) hP (hF.inter hG) (hFc.inter hGc) ⟨x, hxF, hxG⟩
  exact ⟨v, hv, hvFG.1, hvFG.2⟩

/-- A fixed feasible face-covered sequence needs vertex endpoints only.
Interior checkpoints are rounded simultaneously, preserving every available
face incidence and charging each face once. The actual face budgets remain
explicit hypotheses. -/
theorem route_of_feasible_face_covered_sequence
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ P)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  obtain ⟨r, hrP, hrfix, hrF⟩ := face_preserving_vertex_selection P F hP hF hclosed
  have hroute := route_of_face_covered_sequence P F B hF hD (fun k => r (w k)) L
    (fun k hk => hrP (w k) (hfeas k hk)) (by
      intro k hk
      obtain ⟨i, hi, hi'⟩ := hcover k hk
      exact ⟨i, hrF i (w k) hi, hrF i (w (k + 1)) hi'⟩)
  simpa only [hrfix (w 0) h0, hrfix (w L) hL] using hroute

/-- PR #48 start containment with feasible, possibly nonvertex marked
checkpoints. Membership in the closed parent faces supplies feasibility.
Only the two route endpoints must already be parent vertices. Unmarked
interiors of the old sequence need not be feasible. -/
theorem route_of_face_interval_cover_of_feasible_start_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  obtain ⟨r, hrP, hrfix, hrF⟩ := face_preserving_vertex_selection P F hP hF hclosed
  have hroute := route_of_face_interval_cover_of_start_containment
    P F B hF hD s t (fun k => r (w k)) L hbound
    (fun i => ⟨hrP (w (s i)) ((hF i).subset (hends i).1),
      hrP (w (t i)) ((hF i).subset (hends i).2)⟩)
    (fun i => ⟨hrF i (w (s i)) (hends i).1, hrF i (w (t i)) (hends i).2⟩)
    hcover (fun i j hs ht => hrF i (w (s j)) (hcontain i j hs ht))
  simpa only [hrfix (w 0) h0, hrfix (w L) hL] using hroute

/-- The active-containment corollary likewise needs no intermediate vertex
hypothesis. This does not assert that an evolving polytope's faces have
nonempty intersections in the fixed parent, or that their costs are small. -/
theorem route_of_face_interval_cover_of_feasible_active_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hvalid : ∀ i, s i ≤ t i) (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover_of_feasible_start_containment
    P F B hP hF hclosed hD s t w L hbound h0 hL
    (fun i => ⟨hactive i (s i) (Nat.le_refl _) (hvalid i),
      hactive i (t i) (hvalid i) (Nat.le_refl _)⟩) hcover
  intro i j hs ht
  exact hactive i (s j) hs ht


end HirschRegionRoute
end


-- BEGIN Solutions/PolynomialRadialClipCells.lean

open Set

noncomputable section

namespace HirschRadial

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Retraction toward one fixed feasible centre. The scale will be the maximum
of 1 and the normalized final-cut violations, never a stage-dependent scale. -/
def point (o x : E) (μ : ℝ) : E := o + μ⁻¹ • (x - o)

lemma eval_point (f : E →ₗ[ℝ] ℝ) (o x : E) (μ : ℝ) :
    f (point o x μ) = f o + μ⁻¹ * (f x - f o) := by
  simp [point]

lemma point_mem_convex (Q : Set E) (hQ : Convex ℝ Q)
    {o x : E} (ho : o ∈ Q) (hx : x ∈ Q) {μ : ℝ} (hμ : 1 ≤ μ) :
    point o x μ ∈ Q := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have hi : 0 ≤ μ⁻¹ := inv_nonneg.mpr hpos.le
  have hiμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hpos.ne'
  have hi1 : μ⁻¹ ≤ 1 := by
    nlinarith [mul_nonneg hi (sub_nonneg.mpr hμ)]
  have h := hQ ho hx (sub_nonneg.mpr hi1) hi (by ring : (1 - μ⁻¹) + μ⁻¹ = 1)
  have heq : (1 - μ⁻¹) • o + μ⁻¹ • x = point o x μ := by
    dsimp [point]
    module
  rwa [heq] at h

lemma point_satisfies_cut (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    {μ : ℝ} (hμ : 1 ≤ μ) (hbound : f x - f o ≤ μ * (b - f o)) :
    f (point o x μ) ≤ b := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at h
  rw [eval_point]
  linarith

lemma point_on_active_cut (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    {μ : ℝ} (hμ : 1 ≤ μ) (hactive : f x - f o = μ * (b - f o)) :
    f (point o x μ) = b := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  rw [eval_point, hactive, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  ring

lemma point_at_unit_scale (o x : E) : point o x 1 = x := by
  simp [point]

/-- The largest normalized violation is attained, including the no-cut case.
This uses a maximum over an augmented finite family containing the constant 1. -/
theorem finite_radial_scale_exists {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    ∃ μ : ℝ, 1 ≤ μ ∧ (∀ i, r i ≤ μ) ∧ (μ = 1 ∨ ∃ i, μ = r i) := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image r)
  have hne : s.Nonempty := ⟨1, by simp [s]⟩
  refine ⟨s.max' hne, Finset.le_max' s 1 (by simp [s]), ?_, ?_⟩
  · intro i
    apply Finset.le_max'
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))
  · have hm := Finset.max'_mem s hne
    rcases Finset.mem_insert.mp hm with h | h
    · exact Or.inl h
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨i, hi.symm⟩

/-- Normalized dominance gives a point of the final clipped parent.
Strict final-cut slack is explicit; no moving-stage face is used. -/
theorem point_mem_final_clip {ι : Type*}
    (Q : Set E) (hQ : Convex ℝ Q) (f : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (o x : E) (ho : o ∈ Q) (hx : x ∈ Q)
    (hstrict : ∀ i, f i o < b i) {μ : ℝ} (hμ : 1 ≤ μ)
    (hmax : ∀ i, (f i x - f i o) / (b i - f i o) ≤ μ) :
    point o x μ ∈ Q ∩ {y | ∀ i, f i y ≤ b i} := by
  refine ⟨point_mem_convex Q hQ ho hx hμ, ?_⟩
  intro i
  apply point_satisfies_cut (f i) (b i) o x hμ
  exact (div_le_iff₀ (sub_pos.mpr (hstrict i))).mp (hmax i)

/-- The active row really is a final supporting face, not merely a label. -/
theorem point_mem_active_final_face (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    (hstrict : f o < b) {μ : ℝ} (hμ : 1 ≤ μ)
    (hactive : μ = (f x - f o) / (b - f o)) :
    f (point o x μ) = b := by
  apply point_on_active_cut f b o x hμ
  rw [hactive, div_mul_cancel₀ _ (sub_pos.mpr hstrict).ne']

/-- An affine dominance inequality checked at both ends holds throughout a
cell. This is why the exact checker certifies whole cells, not sampled points. -/
theorem affine_dominance_on_cell {a₀ a₁ b₀ b₁ t : ℝ}
    (h0 : a₀ ≤ b₀) (h1 : a₁ ≤ b₁) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * a₀ + t * a₁ ≤ (1 - t) * b₀ + t * b₁ := by
  exact add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left h1 ht0)


end HirschRadial
end


-- BEGIN Solutions/PolynomialContinuousRepair.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A connected trace covered by finitely many closed sets forces its endpoint
labels to be connected in the actual set-intersection graph. -/
theorem region_walk_of_preconnected_closed_cover
    {V ι : Type*} [TopologicalSpace V] [Fintype ι]
    (S : ι → Set V) (hc : ∀ i, IsClosed (S i))
    (T : Set V) (hT : IsPreconnected T)
    (hcover : ∀ x ∈ T, ∃ i, x ∈ S i)
    {i j : ι} {u v : V} (huT : u ∈ T) (hvT : v ∈ T)
    (hu : u ∈ S i) (hv : v ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  classical
  by_contra hn
  let A : Set ι := {k | Nonempty ((intersectionGraph S).Walk i k)}
  let U : Set V := ⋃ k, ⋃ (_ : k ∈ A), S k
  let W : Set V := ⋃ k, ⋃ (_ : k ∉ A), S k
  have hU : IsClosed U :=
    isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hc k
  have hW : IsClosed W :=
    isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hc k
  have hcov : T ⊆ U ∪ W := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x hx
    by_cases ha : k ∈ A
    · exact Or.inl (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨ha, hk⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨ha, hk⟩⟩)
  have hiA : i ∈ A := ⟨.nil⟩
  have hjA : j ∉ A := hn
  obtain ⟨z, _, hzU, hzW⟩ := isPreconnected_closed_iff.mp hT U W hU hW hcov
    ⟨u, huT, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiA, hu⟩⟩⟩
    ⟨v, hvT, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjA, hv⟩⟩⟩
  obtain ⟨k, hkA, hzk⟩ := mem_iUnion.mp hzU |>.imp fun k h => mem_iUnion.mp h
  obtain ⟨l, hlA, hzl⟩ := mem_iUnion.mp hzW |>.imp fun l h => mem_iUnion.mp h
  obtain ⟨p⟩ := hkA
  obtain ⟨q⟩ := shared_point_walk S hzk hzl
  exact hlA ⟨p.append q⟩

/-- Closed extreme faces covering a connected feasible trace suffice. Ordinary
intersection points become parent vertices by compactness. -/
theorem route_of_preconnected_closed_face_cover
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hc : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (T : Set (EuclideanSpace ℝ (Fin d))) (hT : IsPreconnected T)
    (hcover : ∀ x ∈ T, ∃ i, x ∈ F i)
    (u v : EuclideanSpace ℝ (Fin d))
    (huT : u ∈ T) (hvT : v ∈ T)
    (huP : u ∈ extremePoints ℝ P) (hvP : v ∈ extremePoints ℝ P) :
    Route (Adj P) (∑ i, B i) u v := by
  obtain ⟨i, hui⟩ := hcover u huT
  obtain ⟨j, hvj⟩ := hcover v hvT
  obtain ⟨p⟩ := region_walk_of_preconnected_closed_cover F hc T hT hcover huT hvT hui hvj
  let S := fun i => extremePoints ℝ P ∩ F i
  have q : Nonempty ((intersectionGraph S).Walk i j) := by
    clear hui hvj
    induction p with
    | nil => exact ⟨.nil⟩
    | @cons a b c hab p ih =>
      obtain ⟨x, hxa, hxb⟩ := hab.2
      obtain ⟨z, hzP, hza, hzb⟩ := compact_faces_shared_point_portal
        P (F a) (F b) hP (hF a) (hF b) (hc a) (hc b) x hxa hxb
      obtain ⟨q⟩ := ih
      exact ⟨.cons ⟨hab.1, z, ⟨hzP, hza⟩, ⟨hzP, hzb⟩⟩ q⟩
  exact route_of_connected_regions (Adj P) S B
    (fun k => extreme_face_region P (F k) (B k) (hF k) (hD k))
    q u v ⟨huP, hui⟩ ⟨hvP, hvj⟩


end HirschRegionRoute

namespace HirschRadial

/-- A finite maximum including the constant one. -/
def gauge {V ι : Type*} : List ι → (ι → V → ℝ) → V → ℝ
  | [], _, _ => 1
  | i :: l, r, x => max (r i x) (gauge l r x)

lemma gauge_ge_one {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V) :
    1 ≤ gauge l r x := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact ih.trans (le_max_right _ _)

lemma le_gauge {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V)
    {i : ι} (hi : i ∈ l) : r i x ≤ gauge l r x := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_max_left _ _
    · exact (ih hi).trans (le_max_right _ _)

lemma gauge_attains {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V) :
    gauge l r x = 1 ∨ ∃ i ∈ l, gauge l r x = r i x := by
  induction l with
  | nil => exact Or.inl rfl
  | cons i l ih =>
    by_cases h : r i x ≤ gauge l r x
    · rw [gauge, max_eq_right h]
      rcases ih with h1 | ⟨j, hj, heq⟩
      · exact Or.inl h1
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, heq⟩
    · rw [gauge, max_eq_left (le_of_not_ge h)]
      exact Or.inr ⟨i, by simp, rfl⟩

lemma gauge_eq_one {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V)
    (h : ∀ i ∈ l, r i x ≤ 1) : gauge l r x = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [gauge, ih (fun j hj => h j (List.mem_cons_of_mem i hj))]
    exact max_eq_right (h i (by simp))

lemma continuous_gauge {V ι : Type*} [TopologicalSpace V]
    (l : List ι) (r : ι → V → ℝ) (h : ∀ i, Continuous (r i)) :
    Continuous (gauge l r) := by
  induction l with
  | nil => exact continuous_const
  | cons i l ih => exact (h i).max ih

variable {d : ℕ} {ι : Type*} [Fintype ι]

abbrev ClipSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

def finalClip (Q : Set (ClipSpace d)) (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) :=
  Q ∩ {x | ∀ i, f i x ≤ b i}

def normalized (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d)
    (i : ι) (x : ClipSpace d) : ℝ := (f i x - f i o) / (b i - f i o)

def scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) : ℝ :=
  gauge Finset.univ.toList (normalized f b o) x

def retract (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) : ClipSpace d :=
  point o x (scale f b o x)

lemma scale_ge_one (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) :
    1 ≤ scale f b o x := gauge_ge_one _ _ _

lemma normalized_le_scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o x : ClipSpace d) (i : ι) : normalized f b o i x ≤ scale f b o x := by
  apply le_gauge
  simp

lemma continuous_scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d) :
    Continuous (scale f b o) := by
  apply continuous_gauge
  intro i
  exact ((f i).continuous.sub continuous_const).div_const _

lemma continuous_retract (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d) :
    Continuous (retract f b o) := by
  have hi : Continuous (fun x => (scale f b o x)⁻¹) :=
    (continuous_scale f b o).inv₀ fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (scale_ge_one f b o x))
  exact continuous_const.add (hi.smul (continuous_id.sub continuous_const))

lemma retract_mem (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (ho : o ∈ Q) (hx : x ∈ Q) (hs : ∀ i, f i o < b i) :
    retract f b o x ∈ finalClip Q f b :=
  point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b o x ho hx hs
    (scale_ge_one f b o x) (normalized_le_scale f b o x)

lemma retract_fixes (Q : Set (ClipSpace d))
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (hs : ∀ i, f i o < b i) (hx : x ∈ finalClip Q f b) :
    retract f b o x = x := by
  have hm : scale f b o x = 1 := by
    apply gauge_eq_one
    intro i _
    apply (div_le_iff₀ (sub_pos.mpr (hs i))).mpr
    simpa using sub_le_sub_right (hx.2 i) (f i o)
  change point o x (scale f b o x) = x
  rw [hm, point_at_unit_scale]

lemma retract_eq_self_or_on_cut
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (hs : ∀ i, f i o < b i) :
    retract f b o x = x ∨ ∃ i, f i (retract f b o x) = b i := by
  rcases gauge_attains Finset.univ.toList (normalized f b o) x with h | ⟨i, _, hi⟩
  · left
    change point o x (scale f b o x) = x
    rw [show scale f b o x = 1 from h, point_at_unit_scale]
  · right
    exact ⟨i, point_mem_active_final_face (f i).toLinearMap (b i) o x (hs i)
      (scale_ge_one f b o x) hi⟩


end HirschRadial
end


-- BEGIN Solutions/PolynomialSimultaneousClipping.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRadial

variable {d : ℕ}

lemma segment_collinear (a b : ClipSpace d) : Collinear ℝ (segment ℝ a b) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a, b - a, ?_⟩
  intro x hx
  obtain ⟨s, t, _, _, hst, rfl⟩ := hx
  refine ⟨t, ?_⟩
  change s • a + t • b = t • (b - a) + a
  have hs : s = 1 - t := by linarith
  rw [hs]
  module

/-- Any convex collinear set has graph diameter at most one, even without
compactness. If it has two distinct extreme points, they span the entire set. -/
theorem diamLE_one_of_convex_collinear
    (S : Set (ClipSpace d)) (hS : Convex ℝ S) (hcol : Collinear ℝ S) : DiamLE S 1 := by
  intro u hu v hv
  by_cases huv : u = v
  · exact HirschRegionRoute.route_one (Adj S) (Or.inl huv)
  have hEq : S = segment ℝ u v := by
    apply Subset.antisymm ?_ (hS.segment_subset hu.1 hv.1)
    intro x hx
    have h3 : Collinear ℝ ({u, x, v} : Set (ClipSpace d)) :=
      hcol.subset (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hu.1, hx, hv.1⟩)
    rcases h3.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact h.mem_segment
    · rcases (mem_extremePoints_iff_forall_segment.mp hv).2 x hx u hu.1 h.mem_segment with h | h
      · simpa [h] using (right_mem_segment ℝ u v)
      · exact False.elim (huv h)
    · rcases (mem_extremePoints_iff_forall_segment.mp hu).2 v hv.1 x hx h.mem_segment with h | h
      · exact False.elim (huv h.symm)
      · simpa [h] using (left_mem_segment ℝ u v)
  apply HirschRegionRoute.route_one (Adj S)
  right
  refine ⟨huv, ?_⟩
  rw [← hEq]
  exact IsExtreme.refl ℝ S

/-- Clipping an old edge produces a closed extreme face of diameter at most
one. The same proof covers a retained singleton and an empty clipped edge. -/
theorem clipped_segment_face
    (P Q : Set (ClipSpace d)) (hPQ : P ⊆ Q) (hP : IsCompact P) (hPc : Convex ℝ P)
    (a b : ClipSpace d) (hE : IsExtreme ℝ Q (segment ℝ a b)) :
    IsExtreme ℝ P (P ∩ segment ℝ a b) ∧
      IsClosed (P ∩ segment ℝ a b) ∧ DiamLE (P ∩ segment ℝ a b) 1 := by
  have hclosed : IsClosed (segment ℝ a b) := by
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  refine ⟨?_, hP.isClosed.inter hclosed, ?_⟩
  · refine ⟨inter_subset_left, ?_⟩
    intro x hx y hy z hz hseg
    exact ⟨hx, hE.left_mem_of_mem_openSegment (hPQ hx) (hPQ hy) hz.2 hseg⟩
  · exact diamLE_one_of_convex_collinear _ (hPc.inter (convex_segment a b))
      ((segment_collinear a b).subset inter_subset_right)

lemma supporting_cut_extreme
    (P : Set (ClipSpace d)) (f : ClipSpace d →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, f x ≤ c) : IsExtreme ℝ P (P ∩ {x | f x = c}) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  by_contra hne
  have hlt : f x < c := lt_of_le_of_ne (hbound x hx) hne
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have he' := congrArg f he
  simp only [map_add, map_smul, smul_eq_mul] at he'
  rw [hz.2] at he'
  have hlt' := add_lt_add_of_lt_of_le
    (mul_lt_mul_of_pos_left hlt ha)
    (mul_le_mul_of_nonneg_left (hbound y hy) hb.le)
  rw [← add_mul, hab, one_mul] at hlt'
  linarith

variable {ι : Type*} [Fintype ι]

lemma finalClip_convex (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) : Convex ℝ (finalClip Q f b) := by
  intro x hx y hy a c ha hc hac
  refine ⟨hQ hx.1 hy.1 ha hc hac, ?_⟩
  intro i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a * f i x + c * f i y ≤ a * b i + c * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 i) ha) (mul_le_mul_of_nonneg_left (hy.2 i) hc)
    _ = b i := by rw [← add_mul, hac, one_mul]

/-- The complete geometric trace of an old walk, including the zero-step case. -/
def edgeTrace (w : ℕ → ClipSpace d) : ℕ → Set (ClipSpace d)
  | 0 => {w 0}
  | L + 1 => edgeTrace w L ∪ segment ℝ (w L) (w (L + 1))

lemma edgeTrace_start (w : ℕ → ClipSpace d) (L : ℕ) : w 0 ∈ edgeTrace w L := by
  induction L with
  | zero => rfl
  | succ L ih => exact Or.inl ih

lemma edgeTrace_end (w : ℕ → ClipSpace d) (L : ℕ) : w L ∈ edgeTrace w L := by
  cases L with
  | zero => rfl
  | succ L => exact Or.inr (right_mem_segment ℝ _ _)

lemma edgeTrace_preconnected (w : ℕ → ClipSpace d) (L : ℕ) :
    IsPreconnected (edgeTrace w L) := by
  induction L with
  | zero => exact isPreconnected_singleton
  | succ L ih =>
    exact ih.union' ⟨w L, edgeTrace_end w L, left_mem_segment ℝ _ _⟩
      (convex_segment _ _).isPreconnected

lemma edgeTrace_cases (w : ℕ → ClipSpace d) (L : ℕ) {x : ClipSpace d}
    (hx : x ∈ edgeTrace w L) : x = w 0 ∨ ∃ k < L, x ∈ segment ℝ (w k) (w (k + 1)) := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    rcases hx with hx | hx
    · rcases ih hx with h | ⟨k, hk, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hx⟩
    · exact Or.inr ⟨L, by omega, hx⟩

lemma edgeTrace_covered (w : ℕ → ClipSpace d) (L : ℕ) (hL : 0 < L)
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    ∃ k : Fin L, x ∈ segment ℝ (w k) (w (k + 1)) := by
  rcases edgeTrace_cases w L hx with h | ⟨k, hk, hx⟩
  · exact ⟨⟨0, hL⟩, h ▸ left_mem_segment ℝ _ _⟩
  · exact ⟨⟨k, hk⟩, hx⟩

/-- End-to-end simultaneous clipping. Every final cut face is charged once,
not once per old-edge crossing or deformation event. The old walk may contain
stays. Q need only be convex, P compact, and the centre strictly feasible for
the added cuts. No finite-cell cover is assumed: continuity constructs the
needed connected trace and actual fixed-parent support intersections. -/
theorem simultaneous_clip_route
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hP : IsCompact (finalClip Q f b))
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i))
    (w : ℕ → ClipSpace d) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ Q)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)))
    (h0 : w 0 ∈ extremePoints ℝ (finalClip Q f b))
    (hL : w L ∈ extremePoints ℝ (finalClip Q f b)) :
    HirschRegionRoute.Route (Adj (finalClip Q f b)) (L + ∑ i, B i) (w 0) (w L) := by
  classical
  by_cases hzero : L = 0
  · subst L
    exact ⟨fun _ => w 0, rfl, rfl, fun _ _ => Or.inl rfl⟩
  have hpos : 0 < L := Nat.pos_of_ne_zero hzero
  let P := finalClip Q f b
  let F : Sum (Fin L) ι → Set (ClipSpace d) :=
    Sum.elim (fun k => P ∩ segment ℝ (w k) (w (k + 1)))
      (fun i => P ∩ {x | f i x = b i})
  let C : Sum (Fin L) ι → ℕ := Sum.elim (fun _ => 1) B
  have hPc : Convex ℝ P := finalClip_convex Q hQ f b
  have hOld : ∀ k : Fin L,
      IsExtreme ℝ P (F (.inl k)) ∧ IsClosed (F (.inl k)) ∧ DiamLE (F (.inl k)) 1 := by
    intro k
    apply clipped_segment_face P Q (fun _ hx => hx.1) hP hPc
    rcases hsteps k k.isLt with h | h
    · rw [h, segment_same]
      exact isExtreme_singleton.mpr (hverts (k + 1) (by omega))
    · exact h.2
  have hFace : ∀ k, IsExtreme ℝ P (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).1
    | inr i => exact supporting_cut_extreme P (f i) (b i) (fun x hx => hx.2 i)
  have hClosed : ∀ k, IsClosed (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.1
    | inr i => exact hP.isClosed.inter (isClosed_eq (f i).continuous continuous_const)
  have hDiam : ∀ k, DiamLE (F k) (C k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.2
    | inr i => exact hB i
  have hTraceQ : ∀ x ∈ edgeTrace w L, x ∈ Q := by
    intro x hx
    obtain ⟨k, hk⟩ := edgeTrace_covered w L hpos hx
    exact hQ.segment_subset (hverts k (by omega)).1 (hverts (k + 1) (by omega)).1 hk
  let T := retract f b o '' edgeTrace w L
  have hT : IsPreconnected T :=
    (edgeTrace_preconnected w L).image _ (continuous_retract f b o).continuousOn
  have hCover : ∀ y ∈ T, ∃ k, y ∈ F k := by
    rintro y ⟨x, hx, rfl⟩
    have hyP := retract_mem Q hQ f b o x ho (hTraceQ x hx) hs
    rcases retract_eq_self_or_on_cut f b o x hs with heq | ⟨i, hi⟩
    · obtain ⟨k, hk⟩ := edgeTrace_covered w L hpos hx
      exact ⟨.inl k, hyP, heq.symm ▸ hk⟩
    · exact ⟨.inr i, hyP, hi⟩
  have huT : w 0 ∈ T := ⟨w 0, edgeTrace_start w L, retract_fixes Q f b o (w 0) hs h0.1⟩
  have hvT : w L ∈ T := ⟨w L, edgeTrace_end w L, retract_fixes Q f b o (w L) hs hL.1⟩
  have hr := HirschRegionRoute.route_of_preconnected_closed_face_cover
    P F C hP hFace hClosed hDiam T hT hCover (w 0) (w L) huT hvT h0 hL
  simpa [C, Fintype.sum_sum_type] using hr


end HirschRadial
end


-- BEGIN Solutions/PolynomialClippingAttachments.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A vertex strictly inside all added halfspaces was already an outer vertex.
A common small homothety makes both ends of any proposed outer segment feasible. -/
theorem extreme_outer_of_strict_cuts
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (x : ClipSpace d)
    (hx : x ∈ extremePoints ℝ (finalClip Q f b))
    (hsx : ∀ i, f i x < b i) : x ∈ extremePoints ℝ Q := by
  refine ⟨hx.1.1, ?_⟩
  intro y hy z hz hopen
  let μ := max (scale f b x y) (scale f b x z)
  have hμ : 1 ≤ μ := (scale_ge_one f b x y).trans (le_max_left _ _)
  have hyP : point x y μ ∈ finalClip Q f b :=
    point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b x y hx.1.1 hy hsx hμ
      (fun i => (normalized_le_scale f b x y i).trans (le_max_left _ _))
  have hzP : point x z μ ∈ finalClip Q f b :=
    point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b x z hx.1.1 hz hsx hμ
      (fun i => (normalized_le_scale f b x z i).trans (le_max_right _ _))
  have hopen' : x ∈ openSegment ℝ (point x y μ) (point x z μ) := by
    obtain ⟨a, c, ha, hc, hac, he⟩ := hopen
    refine ⟨a, c, ha, hc, hac, ?_⟩
    dsimp [point]
    calc
      a • (x + μ⁻¹ • (y - x)) + c • (x + μ⁻¹ • (z - x)) =
          (a + c) • x + μ⁻¹ • (a • y + c • z - (a + c) • x) := by module
      _ = x := by rw [hac, one_smul, he]; simp
  have he := hx.2 hyP hzP hopen'
  change x + μ⁻¹ • (y - x) = x at he
  have hsmul : μ⁻¹ • (y - x) = 0 := add_left_cancel (he.trans (add_zero x).symm)
  have hμ0 : μ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hμ)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_left (inv_ne_zero hμ0))

/-- Every new vertex lies on an actual final cut. -/
theorem extreme_outer_or_on_final_cut
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (x : ClipSpace d)
    (hx : x ∈ extremePoints ℝ (finalClip Q f b)) :
    x ∈ extremePoints ℝ Q ∨ ∃ i, f i x = b i := by
  classical
  by_cases h : ∃ i, f i x = b i
  · exact Or.inr h
  · left
    apply extreme_outer_of_strict_cuts Q hQ f b x hx
    intro i
    have hne : f i x ≠ b i := fun hi => h ⟨i, hi⟩
    exact lt_of_le_of_ne (hx.1.2 i) hne

/-- A linear functional reaches its outer maximum at an outer extreme point. -/
theorem outer_vertex_above
    (Q : Set (ClipSpace d)) (hQ : IsCompact Q)
    (g : ClipSpace d →L[ℝ] ℝ) (x : ClipSpace d) (hx : x ∈ Q) :
    ∃ a, a ∈ extremePoints ℝ Q ∧ g x ≤ g a := by
  obtain ⟨z, hz, hmax⟩ := hQ.exists_isMaxOn ⟨x, hx⟩ g.continuous.continuousOn
  have hF := supporting_cut_extreme Q g (g z) (fun y hy => hmax hy)
  have hFc : IsClosed (Q ∩ {y | g y = g z}) :=
    hQ.isClosed.inter (isClosed_eq g.continuous continuous_const)
  obtain ⟨a, ha, haF⟩ := HirschRegionRoute.compact_face_point_has_parent_vertex
    Q (Q ∩ {y | g y = g z}) hQ hF hFc ⟨z, hz, rfl⟩
  exact ⟨a, ha, (hmax hx).trans_eq haF.2.symm⟩

/-- A segment going outward through one active cut retracts entirely into the
union of final cut faces. The active label may change, but the family is fixed. -/
theorem outward_segment_retract_on_cut
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (u a : ClipSpace d) (hu : u ∈ finalClip Q f b) (ha : a ∈ Q)
    (i : ι) (hui : f i u = b i) (hai : b i ≤ f i a)
    (x : ClipSpace d) (hx : x ∈ segment ℝ u a) :
    ∃ j, retract f b o x ∈ finalClip Q f b ∧ f j (retract f b o x) = b j := by
  have hxQ : x ∈ Q := hQ.segment_subset hu.1 ha hx
  have hxP := retract_mem Q hQ f b o x ho hxQ hs
  have hge : b i ≤ f i x := by
    obtain ⟨s, t, hs0, ht0, hst, he⟩ := hx
    have he' := congrArg (f i) he
    simp only [map_add, map_smul, smul_eq_mul] at he'
    rw [hui] at he'
    calc
      b i = (s + t) * b i := by rw [hst, one_mul]
      _ = s * b i + t * b i := add_mul _ _ _
      _ ≤ s * b i + t * f i a :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hai ht0)
      _ = f i x := he'
  rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨j, hj⟩
  · refine ⟨i, hxP, ?_⟩
    rw [he]
    have hle : f i x ≤ b i := by simpa [he] using hxP.2 i
    exact le_antisymm hle hge
  · exact ⟨j, hxP, hj⟩

/-- Every final vertex attaches to the radial image of an outer vertex using
only final cut faces; an already outer vertex needs no attachment at all. -/
theorem final_vertex_attachment
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (u : ClipSpace d) (hu : u ∈ extremePoints ℝ (finalClip Q f b)) :
    ∃ a, a ∈ extremePoints ℝ Q ∧
      (u = a ∨ ∀ x ∈ segment ℝ u a,
        ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i) := by
  rcases extreme_outer_or_on_final_cut Q hQ f b u hu with huQ | ⟨i, hi⟩
  · exact ⟨u, huQ, Or.inl rfl⟩
  · obtain ⟨a, ha, hab⟩ := outer_vertex_above Q hQc (f i) u hu.1.1
    refine ⟨a, ha, Or.inr ?_⟩
    intro x hx
    apply outward_segment_retract_on_cut Q hQ f b o ho hs u a hu.1 ha.1 i hi
    · simpa [hi] using hab
    · exact hx

/-- Stays contribute no new points to the geometric trace. Only genuine old
edges and the initial vertex are needed as supports. -/
lemma edgeTrace_edge_or_start
    (Q : Set (ClipSpace d)) (w : ℕ → ClipSpace d) (L : ℕ)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)))
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    x = w 0 ∨ ∃ k < L, Adj Q (w k) (w (k + 1)) ∧ x ∈ segment ℝ (w k) (w (k + 1)) := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    have hp : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)) :=
      fun k hk => hsteps k (by omega)
    rcases hx with hx | hx
    · rcases ih hp hx with h | ⟨k, hk, hE, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hE, hx⟩
    · rcases hsteps L (by omega) with he | hE
      · have hx' : x = w L := by simpa [← he] using hx
        have hxT : x ∈ edgeTrace w L := hx'.symm ▸ edgeTrace_end w L
        rcases ih hp hxT with h | ⟨k, hk, hE, hx⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, by omega, hE, hx⟩
      · exact Or.inr ⟨L, by omega, hE, hx⟩


end HirschRadial
end


-- BEGIN Solutions/PolynomialExteriorCapClipping.lean

/-! Exterior-cap shortcuts for simultaneous clipping.

The cap is a genuine convex subset of the compact truncated outer parent and
is disjoint from the FINAL polytope. All cap motion retracts to the already
charged final cut faces. No diameter budget for the cap is assumed.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial HirschRegionRoute

noncomputable section
namespace HirschExterior

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Any outer point absent from the final clip retracts to a final cut face. -/
lemma retract_on_cut_of_exterior
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (x : ClipSpace d) (hx : x ∈ Q) (hout : x ∉ finalClip Q f b) :
    ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i := by
  have hy := retract_mem Q hQ f b o x ho hx hs
  rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨i, hi⟩
  · exact False.elim (hout (he ▸ hy))
  · exact ⟨i, hy, hi⟩

/-- A convex exterior cap gives genuine connected traces on the union of
final cut faces, with no intrinsic cap-diameter assumption. -/
theorem exterior_cap_trace
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hG : Convex ℝ G)
    (hGQ : G ⊆ Q) (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b) :
    IsPreconnected (retract f b o '' G) ∧
      ∀ y ∈ retract f b o '' G,
        ∃ i, y ∈ finalClip Q f b ∩ {x | f i x = b i} := by
  refine ⟨hG.isPreconnected.image _ (continuous_retract f b o).continuousOn, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact retract_on_cut_of_exterior Q hQ f b o ho hs x (hGQ hx) (hout x hx)

/-- An exterior jump may be a long segment in the cap. Stays add no new
points; other trace points belong to genuine outer edges or to the cap. -/
lemma exterior_edgeTrace_cases
    (Q G : Set (ClipSpace d)) (hG : Convex ℝ G)
    (w : ℕ → ClipSpace d) (L : ℕ)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨
      Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G))
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    x = w 0 ∨ (∃ k < L, Adj Q (w k) (w (k + 1)) ∧
      x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    have hp : ∀ k < L, w k = w (k + 1) ∨
        Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G) :=
      fun k hk => hsteps k (by omega)
    have lift : x = w 0 ∨ (∃ k < L, Adj Q (w k) (w (k + 1)) ∧
        x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G →
        x = w 0 ∨ (∃ k < L + 1, Adj Q (w k) (w (k + 1)) ∧
        x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G := by
      rintro (h | ⟨k, hk, he, hx⟩ | hg)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, by omega, he, hx⟩)
      · exact Or.inr (Or.inr hg)
    rcases hx with hx | hx
    · exact lift (ih hp hx)
    · rcases hsteps L (by omega) with he | hE | hcap
      · have hx' : x = w L := by simpa [← he] using hx
        exact lift (ih hp (hx'.symm ▸ edgeTrace_end w L))
      · exact Or.inr (Or.inl ⟨L, by omega, hE, hx⟩)
      · exact Or.inr (Or.inr (hG.segment_subset hcap.1 hcap.2 hx))

/-- Full endpoint-attachment assembly allowing arbitrary shortcuts inside one
convex exterior cap. Only genuine edges supply clipped-edge supports. The
cap itself is never a paid region of the final parent. -/
theorem clip_route_with_exterior_attachments
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hP : IsCompact (finalClip Q f b))
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i))
    (u v : ClipSpace d)
    (hu : u ∈ extremePoints ℝ (finalClip Q f b))
    (hv : v ∈ extremePoints ℝ (finalClip Q f b))
    (w : ℕ → ClipSpace d) (L : ℕ) (h0Q : w 0 ∈ extremePoints ℝ Q)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨
      Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G))
    (hAu : u = w 0 ∨ ∀ x ∈ segment ℝ u (w 0),
      ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i)
    (hAv : v = w L ∨ ∀ x ∈ segment ℝ v (w L),
      ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i) :
    Route (Adj (finalClip Q f b)) (L + ∑ i, B i) u v := by
  classical
  let P := finalClip Q f b
  let E : Option (Fin L) → Set (ClipSpace d) := fun k =>
    k.elim (P ∩ {w 0}) (fun k =>
      if Adj Q (w k) (w (k + 1)) then P ∩ segment ℝ (w k) (w (k + 1)) else ∅)
  let F : Sum (Option (Fin L)) ι → Set (ClipSpace d) :=
    Sum.elim E (fun i => P ∩ {x | f i x = b i})
  let C : Sum (Option (Fin L)) ι → ℕ :=
    Sum.elim (fun k => k.elim 0 (fun _ => 1)) B
  have hPc : Convex ℝ P := finalClip_convex Q hQ f b
  have hOld : ∀ k : Option (Fin L),
      IsExtreme ℝ P (E k) ∧ IsClosed (E k) ∧ DiamLE (E k) (k.elim 0 (fun _ => 1)) := by
    intro k
    cases k with
    | none =>
      have hS : IsExtreme ℝ Q {w 0} := isExtreme_singleton.mpr h0Q
      refine ⟨⟨inter_subset_left, ?_⟩, hP.isClosed.inter isClosed_singleton, ?_⟩
      · intro x hx y hy z hz hseg
        exact ⟨hx, hS.left_mem_of_mem_openSegment hx.1 hy.1 hz.2 hseg⟩
      · intro x hx y hy
        have he : x = y := (show x = w 0 from hx.1.2).trans (show y = w 0 from hy.1.2).symm
        exact ⟨fun _ => x, rfl, he, by intro k hk; change k < 0 at hk; omega⟩
    | some k =>
      by_cases h : Adj Q (w k) (w (k + 1))
      · simpa [E, h] using clipped_segment_face P Q (fun _ hx => hx.1) hP hPc (w k) (w (k + 1)) h.2
      · have he : IsExtreme ℝ P (∅ : Set (ClipSpace d)) :=
          ⟨empty_subset _, by intro x hx y hy z hz; exact False.elim hz⟩
        have hd : DiamLE (∅ : Set (ClipSpace d)) 1 := by
          intro x hx
          exact False.elim hx.1
        simpa [E, h] using (show IsExtreme ℝ P (∅ : Set (ClipSpace d)) ∧
          IsClosed (∅ : Set (ClipSpace d)) ∧ DiamLE (∅ : Set (ClipSpace d)) 1 from ⟨he, isClosed_empty, hd⟩)
  have hFace : ∀ k, IsExtreme ℝ P (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).1
    | inr i => exact supporting_cut_extreme P (f i) (b i) (fun x hx => hx.2 i)
  have hClosed : ∀ k, IsClosed (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.1
    | inr i => exact hP.isClosed.inter (isClosed_eq (f i).continuous continuous_const)
  have hDiam : ∀ k, DiamLE (F k) (C k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.2
    | inr i => exact hB i
  have hMidQ : ∀ x ∈ edgeTrace w L, x ∈ Q := by
    intro x hx
    rcases exterior_edgeTrace_cases Q G hG w L hsteps hx with he | ⟨k, hk, hE, hx⟩ | hxG
    · exact he.symm ▸ h0Q.1
    · exact hE.2.subset hx
    · exact hGQ hxG
  have hMidCover : ∀ x ∈ edgeTrace w L, ∃ k, retract f b o x ∈ F k := by
    intro x hx
    have hyP := retract_mem Q hQ f b o x ho (hMidQ x hx) hs
    rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨i, hi⟩
    · rcases exterior_edgeTrace_cases Q G hG w L hsteps hx with hx0 | ⟨k, hk, hE, hxE⟩ | hxG
      · exact ⟨.inl none, hyP, he.trans hx0⟩
      · refine ⟨.inl (some ⟨k, hk⟩), ?_⟩
        change retract f b o x ∈ if Adj Q (w k) (w (k + 1)) then P ∩ segment ℝ (w k) (w (k + 1)) else ∅
        rw [if_pos hE]
        exact ⟨hyP, he.symm ▸ hxE⟩
      · exact False.elim (hout x hxG (he ▸ hyP))
    · exact ⟨.inr i, hyP, hi⟩
  let K := (segment ℝ u (w 0) ∪ edgeTrace w L) ∪ segment ℝ (w L) v
  have hK : IsPreconnected K :=
    ((convex_segment u (w 0)).isPreconnected.union'
      ⟨w 0, right_mem_segment ℝ _ _, edgeTrace_start w L⟩ (edgeTrace_preconnected w L)).union'
      ⟨w L, Or.inr (edgeTrace_end w L), left_mem_segment ℝ _ _⟩
      (convex_segment (w L) v).isPreconnected
  let T := retract f b o '' K
  have hT : IsPreconnected T := hK.image _ (continuous_retract f b o).continuousOn
  have hCover : ∀ y ∈ T, ∃ k, y ∈ F k := by
    rintro y ⟨x, hx, rfl⟩
    rcases hx with (hx | hx) | hx
    · rcases hAu with he | hAu
      · have hx0 : x = w 0 := by simpa [he] using hx
        exact hMidCover x (hx0.symm ▸ edgeTrace_start w L)
      · obtain ⟨i, hi, he⟩ := hAu x hx
        exact ⟨.inr i, hi, he⟩
    · exact hMidCover x hx
    · rcases hAv with he | hAv
      · have hxL : x = w L := by simpa [he] using hx
        exact hMidCover x (hxL.symm ▸ edgeTrace_end w L)
      · have hx' : x ∈ segment ℝ v (w L) := by rwa [segment_symm]
        obtain ⟨i, hi, he⟩ := hAv x hx'
        exact ⟨.inr i, hi, he⟩
  have huT : u ∈ T :=
    ⟨u, Or.inl (Or.inl (left_mem_segment ℝ _ _)), retract_fixes Q f b o u hs hu.1⟩
  have hvT : v ∈ T :=
    ⟨v, Or.inr (right_mem_segment ℝ _ _), retract_fixes Q f b o v hs hv.1⟩
  have hr := route_of_preconnected_closed_face_cover
    P F C hP hFace hClosed hDiam T hT hCover u v huT hvT hu hv
  simpa [C, Fintype.sum_sum_type, Fintype.sum_option] using hr

/-- Diameter transfer using actual outer edges and convex exterior-cap
shortcuts. New final vertices are lifted by compact optimization, not assumed
already connected. No cap-diameter budget occurs in the conclusion. -/
theorem clip_diameter_from_exterior_routes
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ)
    (hD : ∀ a ∈ extremePoints ℝ Q, ∀ c ∈ extremePoints ℝ Q,
      Route (fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)) D a c)
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + ∑ i, B i) := by
  have hCuts : IsClosed {x : ClipSpace d | ∀ i, f i x ≤ b i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (f i).continuous continuous_const
  have hP : IsCompact (finalClip Q f b) := hQc.inter_right hCuts
  intro u hu v hv
  obtain ⟨a, ha, hAu⟩ := final_vertex_attachment Q hQ hQc f b o ho hs u hu
  obtain ⟨c, hc, hAv⟩ := final_vertex_attachment Q hQ hQc f b o ho hs v hv
  obtain ⟨w, hw0, hwD, hwsteps⟩ := hD a ha c hc
  apply clip_route_with_exterior_attachments Q G hQ hG hGQ f b o ho hs hP hout B hB u v hu hv w D
  · simpa only [hw0] using ha
  · exact hwsteps
  · simpa only [hw0] using hAu
  · simpa only [hwD] using hAv

/-- The structural cap condition adds at most ONE step. Both cap endpoints
can be connected directly through the cap, so two ray charges are unnecessary. -/
theorem exterior_cap_augmented_route_bound
    (Q G V : Set (ClipSpace d)) (D : ℕ)
    (hOld : ∀ a ∈ V, ∀ c ∈ V, Route (Adj Q) D a c)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj Q a x)) :
    ∀ u ∈ extremePoints ℝ Q, ∀ v ∈ extremePoints ℝ Q,
      Route (fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)) (D + 1) u v := by
  let R := fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)
  have hOldR : ∀ a ∈ V, ∀ c ∈ V, Route R D a c := by
    intro a ha c hc
    obtain ⟨w, h0, hD, hsteps⟩ := hOld a ha c hc
    refine ⟨w, h0, hD, ?_⟩
    intro k hk
    exact (hsteps k hk).imp id Or.inl
  have pad : ∀ {a c : ClipSpace d} {N : ℕ}, N ≤ D + 1 → Route R N a c → Route R (D + 1) a c := by
    intro a c N hle ⟨w, h0, hN, hs⟩
    exact HirschProduct.pad_walk R hle w h0 hN hs
  have cat : ∀ {a c z : ClipSpace d} {M N : ℕ},
      Route R M a c → Route R N c z → Route R (M + N) a z := by
    intro a c z M N ⟨w, h0, hM, hw⟩ ⟨q, hq0, hqN, hq⟩
    exact HirschProduct.append_walk R w q h0 hM hq0 hqN hw hq
  intro u hu v hv
  rcases hclass u hu with huV | ⟨huG, a, haV, hau⟩
  · rcases hclass v hv with hvV | ⟨hvG, c, hcV, hcv⟩
    · exact pad (by omega) (hOldR u huV v hvV)
    · exact cat (hOldR u huV c hcV) (route_one R (Or.inr (Or.inl hcv)))
  · rcases hclass v hv with hvV | ⟨hvG, c, hcV, hcv⟩
    · have hua : Adj Q u a := ⟨hau.1.symm, by simpa [segment_symm] using hau.2⟩
      have hr := cat (route_one R (Or.inr (Or.inl hua))) (hOldR a haV v hvV)
      simpa [Nat.add_comm] using hr
    · exact pad (by omega) (route_one R (Or.inr (Or.inr ⟨huG, hvG⟩)))

/-- End-to-end cap-witness form of pointed unbounded clipping. A sufficiently
far truncation of a pointed polyhedron has exactly this vertex classification:
old vertices route in D steps; every new cap vertex is adjacent to an old one.
The general polyhedral existence of that truncation is NOT proved in this file.
All final-face costs remain explicit. -/
theorem simultaneous_clip_diameter_from_exterior_cap
    (Q G V : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ) (hOld : ∀ a ∈ V, ∀ c ∈ V, Route (Adj Q) D a c)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj Q a x))
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + 1 + ∑ i, B i) := by
  exact clip_diameter_from_exterior_routes Q G hQ hQc hG hGQ f b o ho hs hout
    (D + 1) (exterior_cap_augmented_route_bound Q G V D hOld hclass) B hB


end HirschExterior
end


-- BEGIN Solutions/Sol_Hirsch_exterior_cap_clip_diameter.lean

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

/-- Public-type offline wrapper. The structural exterior cap and strict centre
are explicit hypotheses; this is not the unrestricted pointed H-polyhedron
existence/classification theorem. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (R G V : Set (EuclideanSpace ℝ (Fin d)))
    (hR : Convex ℝ R) (hRc : IsCompact R)
    (hG : Convex ℝ G) (hGR : G ⊆ R)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ R) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ R ∩ {y | ∀ i, f i y ≤ b i})
    (D : ℕ)
    (hOld : ∀ a ∈ V, ∀ c ∈ V,
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = a ∧ w D = c ∧
        ∀ k < D, w k = w (k + 1) ∨ Adj R (w k) (w (k + 1)))
    (hclass : ∀ x ∈ extremePoints ℝ R,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj R a x))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE ((R ∩ {y | ∀ j, f j y ≤ b j}) ∩ {x | f i x = b i}) (B i)) :
    DiamLE (R ∩ {y | ∀ i, f i y ≤ b i}) (D + 1 + ∑ i, B i) := by
  exact HirschExterior.simultaneous_clip_diameter_from_exterior_cap
    R G V hR hRc hG hGR f b o ho hs hout D hOld hclass B hB


#print axioms solution
