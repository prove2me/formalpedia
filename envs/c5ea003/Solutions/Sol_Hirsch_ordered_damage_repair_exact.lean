-- Prove2me | solution 1 for Hirsch.ordered_damage_repair_exact
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-09T14:10:22.374223+00:00
-- url     : https://prove2.me/submissions/795cd02d-fc25-412e-942b-0d05e823e41a

import Definitions.Def_Hirsch_model
import Mathlib

set_option maxHeartbeats 8000000

-- BEGIN Solutions.PolynomialProductWalk

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

-- BEGIN Solutions.PolynomialFaceReentrySplice

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

-- BEGIN Solutions.PolynomialProjectiveDamageBlocks

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschFaceSplice

/-- One damage block on an existing parent walk.  The block records an
interval `[s,t]` whose two endpoints lie in an extreme face `F` of intrinsic
diameter at most `B`. -/
structure PathFaceBlock {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) where
  s : ℕ
  t : ℕ
  B : ℕ
  F : Set (EuclideanSpace ℝ (Fin d))
  hst : s ≤ t
  htL : t ≤ L
  hF : IsExtreme ℝ P F
  hFD : DiamLE F B
  hsP : w s ∈ extremePoints ℝ P
  htP : w t ∈ extremePoints ℝ P
  hsF : w s ∈ F
  htF : w t ∈ F

/-- Sum of the intrinsic face-diameter charges in a list of blocks. -/
def blockBudgetSum {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)} :
    List (PathFaceBlock (L := L) P w) → ℕ
  | [] => 0
  | b :: bs => b.B + blockBudgetSum bs

/-- Ordered blocks do not overlap in the original path: after the current
position, the next block starts no earlier than that position, and recursive
processing resumes at the previous block's last endpoint. -/
def BlocksOrderedFrom {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (pos : ℕ) : List (PathFaceBlock (L := L) P w) → Prop
  | [] => True
  | b :: bs => pos ≤ b.s ∧ BlocksOrderedFrom b.t bs

/-- Amortized suffix repair for a sequence of disjoint face-supported damage
blocks.  Starting at original path position `pos`, all blocks can be replaced
while paying at most one copy of each block's face diameter.  The original
path length outside the selected blocks is never charged twice.

The deliberately loose budget `L-pos + sum B_i` is the useful invariant for
projective-removal applications: it is independent of the number of local
flip events inside any one block. -/
theorem splice_ordered_face_blocks_suffix
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hwL : w L = v)
    (hwstep : ∀ j < L,
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (pos : ℕ) (hposL : pos ≤ L)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom pos blocks) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w pos ∧
      q (L - pos + blockBudgetSum blocks) = v ∧
      ∀ j < L - pos + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  induction blocks generalizing pos with
  | nil =>
      let qs : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      refine ⟨qs, rfl, ?_, ?_⟩
      · have hidx : pos + (L - pos) = L := by omega
        simpa [qs, blockBudgetSum, hidx] using hwL
      · intro j hj
        have hj' : j < L - pos := by simpa [blockBudgetSum] using hj
        have hjL : pos + j < L := by omega
        have h := hwstep (pos + j) hjL
        simpa [qs, blockBudgetSum, Nat.add_assoc] using h
  | cons b bs ih =>
      rcases hord with ⟨hposS, hrest⟩

      let qgap : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      have hgap0 : qgap 0 = w pos := by simp [qgap]
      have hgapB : qgap (b.s - pos) = w b.s := by
        have hidx : pos + (b.s - pos) = b.s := by omega
        simp [qgap, hidx]
      have hgapstep : ∀ j < b.s - pos,
          qgap j = qgap (j + 1) ∨ Adj P (qgap j) (qgap (j + 1)) := by
        intro j hj
        have hltS : pos + j < b.s := by
          calc
            pos + j < pos + (b.s - pos) := Nat.add_lt_add_left hj pos
            _ = b.s := by omega
        have hsL : b.s ≤ L := b.hst.trans b.htL
        have hidx : pos + j < L := hltS.trans_le hsL
        have h := hwstep (pos + j) hidx
        simpa [qgap, Nat.add_assoc] using h

      have hsFext : w b.s ∈ extremePoints ℝ b.F :=
        extreme_in_extreme_face b.hF b.hsP b.hsF
      have htFext : w b.t ∈ extremePoints ℝ b.F :=
        extreme_in_extreme_face b.hF b.htP b.htF
      obtain ⟨qface, hface0, hfaceB, hfacestep⟩ :=
        b.hFD (w b.s) hsFext (w b.t) htFext
      have hfacestepP : ∀ j < b.B,
          qface j = qface (j + 1) ∨ Adj P (qface j) (qface (j + 1)) := by
        intro j hj
        rcases hfacestep j hj with heq | hadj
        · exact Or.inl heq
        · exact Or.inr (face_adj_to_parent b.hF hadj)

      obtain ⟨qrest, hrest0, hrestB, hreststep⟩ :=
        ih b.t b.htL hrest

      obtain ⟨qgf, hgf0, hgfB, hgfstep⟩ :=
        HirschProduct.append_walk (Adj P) qgap qface
          hgap0 hgapB hface0 hfaceB hgapstep hfacestepP
      obtain ⟨qall, hall0, hallB, hallstep⟩ :=
        HirschProduct.append_walk (Adj P) qgf qrest
          hgf0 hgfB hrest0 hrestB hgfstep hreststep

      let K := (b.s - pos) + b.B + (L - b.t + blockBudgetSum bs)
      let M := L - pos + (b.B + blockBudgetSum bs)
      have hsL : b.s ≤ L := b.hst.trans b.htL
      have htail : L - b.t ≤ L - b.s := Nat.sub_le_sub_left b.hst L
      have hposSsum : pos + (b.s - pos) = b.s := by omega
      have hsLsum : b.s + (L - b.s) = L := by omega
      have hposLsum : pos + (L - pos) = L := by omega
      have hsum : (b.s - pos) + (L - b.s) = L - pos := by
        omega
      have hcore : (b.s - pos) + (L - b.t) ≤ L - pos := by
        calc
          (b.s - pos) + (L - b.t) ≤ (b.s - pos) + (L - b.s) :=
            Nat.add_le_add_left htail _
          _ = L - pos := hsum
      have hKM : K ≤ M := by
        dsimp [K, M]
        omega
      obtain ⟨qpad, hpad0, hpadM, hpadstep⟩ :=
        HirschProduct.pad_walk (Adj P) hKM qall hall0 (by
          simpa [K, Nat.add_assoc] using hallB) (by
          simpa [K, Nat.add_assoc] using hallstep)
      refine ⟨qpad, hpad0, ?_, ?_⟩
      · simpa [M, blockBudgetSum, Nat.add_assoc] using hpadM
      · simpa [M, blockBudgetSum, Nat.add_assoc] using hpadstep

/-- Global form: a finite ordered family of disjoint damage blocks on a
length-`L` path can all be repaired for total budget at most
`L + sum_i B_i`.  Thus local damage events are amortized by supporting faces,
not by their raw event count. -/
theorem splice_ordered_face_blocks
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L,
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧
      q (L + blockBudgetSum blocks) = v ∧
      ∀ j < L + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_suffix P u v w hwL hwstep
      0 (Nat.zero_le L) blocks hord
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [hw0] using hq0
  · simpa using hqB
  · simpa using hqstep


end HirschFaceSplice
end

-- BEGIN Solutions.PolynomialProjectiveDamageSurviving

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 7000000

noncomputable section

namespace HirschFaceSplice

/-- An original step index lies outside every half-open damage interval. -/
def StepOutsideBlocks {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w)) (j : ℕ) : Prop :=
  ∀ b, b ∈ blocks → j < b.s ∨ b.t ≤ j

lemma block_start_ge_of_ordered {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    {pos : ℕ} {blocks : List (PathFaceBlock (L := L) P w)}
    (hord : BlocksOrderedFrom pos blocks)
    {b : PathFaceBlock (L := L) P w} (hb : b ∈ blocks) :
    pos ≤ b.s := by
  induction blocks generalizing pos with
  | nil => simp at hb
  | cons c cs ih =>
      change pos ≤ c.s ∧ BlocksOrderedFrom c.t cs at hord
      rcases hord with ⟨hposC, hrest⟩
      simp only [List.mem_cons] at hb
      rcases hb with hbc | hb
      · subst b
        exact hposC
      · have hct : c.t ≤ b.s := ih hrest hb
        exact hposC.trans (c.hst.trans hct)

lemma blockBudgetSum_le_length_mul {d L C : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w))
    (hB : ∀ b ∈ blocks, b.B ≤ C) :
    blockBudgetSum blocks ≤ blocks.length * C := by
  induction blocks with
  | nil => simp [blockBudgetSum]
  | cons b bs ih =>
      have hb : b.B ≤ C := hB b (by simp)
      have htail : ∀ c ∈ bs, c.B ≤ C := by
        intro c hc
        exact hB c (by simp [hc])
      have hadd := Nat.add_le_add hb (ih htail)
      simpa [blockBudgetSum, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hadd

/-- Original step count removed by the selected blocks. -/
def blockRemovedLength {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)} :
    List (PathFaceBlock (L := L) P w) → ℕ
  | [] => 0
  | b :: bs => (b.t - b.s) + blockRemovedLength bs

/-- Exact concatenation budget: surviving gaps plus one face charge per block. -/
def blockRepairLength {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)} (pos : ℕ) :
    List (PathFaceBlock (L := L) P w) → ℕ
  | [] => L - pos
  | b :: bs => (b.s - pos) + b.B + blockRepairLength b.t bs

/-- Ordered intervals cannot remove more original steps than the suffix contains. -/
lemma blockRemovedLength_le {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w))
    (pos : ℕ) (hposL : pos ≤ L) (hord : BlocksOrderedFrom pos blocks) :
    blockRemovedLength blocks ≤ L - pos := by
  induction blocks generalizing pos with
  | nil => simp [blockRemovedLength]
  | cons b bs ih =>
      change pos ≤ b.s ∧ BlocksOrderedFrom b.t bs at hord
      have hi := ih b.t b.htL hord.2
      have hst := b.hst
      have htL := b.htL
      have hposS := hord.1
      have hgap := Nat.sub_add_cancel hposS
      have hblock := Nat.sub_add_cancel hst
      have htail := Nat.sub_add_cancel htL
      have hwhole := Nat.sub_add_cancel hposL
      simp only [blockRemovedLength]
      omega

/-- Conservation of the original length, before natural-number subtraction. -/
lemma blockRepairLength_add_removed {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w))
    (pos : ℕ) (hposL : pos ≤ L) (hord : BlocksOrderedFrom pos blocks) :
    blockRepairLength pos blocks + blockRemovedLength blocks =
      L - pos + blockBudgetSum blocks := by
  induction blocks generalizing pos with
  | nil => simp [blockRepairLength, blockRemovedLength, blockBudgetSum]
  | cons b bs ih =>
      change pos ≤ b.s ∧ BlocksOrderedFrom b.t bs at hord
      have hi := ih b.t b.htL hord.2
      have hgap := Nat.sub_add_cancel hord.1
      have hblock := Nat.sub_add_cancel b.hst
      have htail := Nat.sub_add_cancel b.htL
      have hwhole := Nat.sub_add_cancel hposL
      simp only [blockRepairLength, blockRemovedLength, blockBudgetSum]
      omega

lemma blockRepairLength_eq {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w))
    (pos : ℕ) (hposL : pos ≤ L) (hord : BlocksOrderedFrom pos blocks) :
    blockRepairLength pos blocks =
      (L - pos - blockRemovedLength blocks) + blockBudgetSum blocks := by
  have hle := blockRemovedLength_le blocks pos hposL hord
  have heq := blockRepairLength_add_removed blocks pos hposL hord
  omega

/-- Repair genuinely damaged sequences: no original step inside a block is
assumed valid. The exact budget contains only surviving gaps and face charges. -/
theorem splice_surviving_steps_exact_suffix
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hwL : w L = v)
    (pos : ℕ) (hposL : pos ≤ L)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom pos blocks)
    (hsurvive : ∀ j, pos ≤ j → j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w pos ∧ q (blockRepairLength pos blocks) = v ∧
      ∀ j < blockRepairLength pos blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  induction blocks generalizing pos with
  | nil =>
      let qs : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      refine ⟨qs, rfl, ?_, ?_⟩
      · have hidx : pos + (L - pos) = L := Nat.add_sub_of_le hposL
        simpa [qs, blockRepairLength, hidx] using hwL
      · intro j hj
        have hj' : j < L - pos := by simpa [blockRepairLength] using hj
        have hjL : pos + j < L := by omega
        have hout : StepOutsideBlocks ([] : List (PathFaceBlock (L := L) P w))
            (pos + j) := by
          intro b hb
          simp at hb
        have h := hsurvive (pos + j) (Nat.le_add_right pos j) hjL hout
        simpa [qs, Nat.add_assoc] using h
  | cons b bs ih =>
      change pos ≤ b.s ∧ BlocksOrderedFrom b.t bs at hord
      rcases hord with ⟨hposS, hrest⟩
      let qgap : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      have hgap0 : qgap 0 = w pos := by simp [qgap]
      have hgapB : qgap (b.s - pos) = w b.s := by
        simp [qgap, Nat.add_sub_of_le hposS]
      have hgapstep : ∀ j < b.s - pos,
          qgap j = qgap (j + 1) ∨ Adj P (qgap j) (qgap (j + 1)) := by
        intro j hj
        have hltS : pos + j < b.s := by
          calc
            pos + j < pos + (b.s - pos) := Nat.add_lt_add_left hj pos
            _ = b.s := Nat.add_sub_of_le hposS
        have hjL : pos + j < L := hltS.trans_le (b.hst.trans b.htL)
        have hout : StepOutsideBlocks (b :: bs) (pos + j) := by
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with hcb | hc
          · subst c
            exact Or.inl hltS
          · have hstart : b.t ≤ c.s := block_start_ge_of_ordered hrest hc
            exact Or.inl (hltS.trans_le (b.hst.trans hstart))
        simpa [qgap, Nat.add_assoc] using
          hsurvive (pos + j) (Nat.le_add_right pos j) hjL hout
      obtain ⟨qface, hface0, hfaceB, hfacestep⟩ :=
        b.hFD (w b.s) (extreme_in_extreme_face b.hF b.hsP b.hsF)
          (w b.t) (extreme_in_extreme_face b.hF b.htP b.htF)
      have hfacestepP : ∀ j < b.B,
          qface j = qface (j + 1) ∨ Adj P (qface j) (qface (j + 1)) := by
        intro j hj
        rcases hfacestep j hj with heq | hadj
        · exact Or.inl heq
        · exact Or.inr (face_adj_to_parent b.hF hadj)
      have hsurviveRest : ∀ j, b.t ≤ j → j < L → StepOutsideBlocks bs j →
          w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
        intro j htj hjL hout
        apply hsurvive j (hposS.trans (b.hst.trans htj)) hjL
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with hcb | hc
        · subst c
          exact Or.inr htj
        · exact hout c hc
      obtain ⟨qrest, hrest0, hrestB, hreststep⟩ :=
        ih b.t b.htL hrest hsurviveRest
      obtain ⟨qgf, hgf0, hgfB, hgfstep⟩ :=
        HirschProduct.append_walk (Adj P) qgap qface
          hgap0 hgapB hface0 hfaceB hgapstep hfacestepP
      obtain ⟨qall, hall0, hallB, hallstep⟩ :=
        HirschProduct.append_walk (Adj P) qgf qrest
          hgf0 hgfB hrest0 hrestB hgfstep hreststep
      exact ⟨qall, hall0, hallB, hallstep⟩

/-- Exact global budget: original length minus removed steps plus repair costs.
This does not assume the original sequence was a walk in the repaired polytope. -/
theorem splice_ordered_face_blocks_of_surviving_steps_exact
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L - blockRemovedLength blocks + blockBudgetSum blocks) = v ∧
      ∀ j < L - blockRemovedLength blocks + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_surviving_steps_exact_suffix P v w hwL 0 (Nat.zero_le L) blocks hord
      (fun j _ hj hout => hsurvive j hj hout)
  have hbudget := blockRepairLength_eq blocks 0 (Nat.zero_le L) hord
  simp only [Nat.sub_zero] at hbudget
  rw [hbudget] at hqB hqstep
  exact ⟨q, hq0.trans hw0, hqB, hqstep⟩

/-- Backward-compatible loose suffix bound, derived from the exact repair. -/
theorem splice_ordered_face_blocks_of_surviving_steps_suffix
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hwL : w L = v)
    (pos : ℕ) (hposL : pos ≤ L)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom pos blocks)
    (hsurvive : ∀ j, pos ≤ j → j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w pos ∧ q (L - pos + blockBudgetSum blocks) = v ∧
      ∀ j < L - pos + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_surviving_steps_exact_suffix P v w hwL pos hposL blocks hord hsurvive
  have hid := blockRepairLength_add_removed blocks pos hposL hord
  have hle : blockRepairLength pos blocks ≤ L - pos + blockBudgetSum blocks := by omega
  exact HirschProduct.pad_walk (Adj P) hle q hq0 hqB hqstep

/-- Loose global form retained for callers that do not track removed lengths. -/
theorem splice_ordered_face_blocks_of_surviving_steps
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L + blockBudgetSum blocks) = v ∧
      ∀ j < L + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_of_surviving_steps_exact P u v w hw0 hwL blocks hord hsurvive
  have hle : L - blockRemovedLength blocks + blockBudgetSum blocks ≤
      L + blockBudgetSum blocks := Nat.add_le_add_right (Nat.sub_le _ _) _
  exact HirschProduct.pad_walk (Adj P) hle q hq0 hqB hqstep

/-- At most M damaged intervals of cost at most C, with no interior survival assumption. -/
theorem splice_surviving_steps_uniform
    {d L M C : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hlen : blocks.length ≤ M) (hB : ∀ b ∈ blocks, b.B ≤ C) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L + M * C) = v ∧
      ∀ j < L + M * C,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_of_surviving_steps P u v w hw0 hwL blocks hord hsurvive
  have hsum := blockBudgetSum_le_length_mul blocks hB
  have hmul : blocks.length * C ≤ M * C := Nat.mul_le_mul_right C hlen
  exact HirschProduct.pad_walk (Adj P) (Nat.add_le_add_left (hsum.trans hmul) L)
    q hq0 hqB hqstep

/-- Compatibility wrapper. For new applications use the surviving-steps theorem. -/
theorem splice_ordered_face_blocks_uniform
    {d L M C : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hlen : blocks.length ≤ M) (hB : ∀ b ∈ blocks, b.B ≤ C) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L + M * C) = v ∧
      ∀ j < L + M * C,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  exact splice_surviving_steps_uniform P u v w hw0 hwL blocks hord
    (fun j hj _ => hwstep j hj) hlen hB

/-- Aggregate savings suffice: individual repairs may grow provided their total
cost does not exceed the number of original steps removed. -/
theorem splice_surviving_steps_no_growth
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hcost : blockBudgetSum blocks ≤ blockRemovedLength blocks) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q L = v ∧
      ∀ j < L, q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_of_surviving_steps_exact P u v w hw0 hwL blocks hord hsurvive
  have hremoved := blockRemovedLength_le blocks 0 (Nat.zero_le L) hord
  simp only [Nat.sub_zero] at hremoved
  have hle : L - blockRemovedLength blocks + blockBudgetSum blocks ≤ L := by omega
  exact HirschProduct.pad_walk (Adj P) hle q hq0 hqB hqstep


end HirschFaceSplice
end

-- BEGIN Solutions.Sol_Hirsch_ordered_damage_repair

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschFaceSplice

noncomputable section

namespace HirschDamagePublic

lemma ordered_of_pairwise {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w)) (pos : ℕ)
    (hpos : ∀ b ∈ blocks, pos ≤ b.s)
    (hp : blocks.Pairwise (fun a b => a.t ≤ b.s)) :
    BlocksOrderedFrom pos blocks := by
  induction blocks generalizing pos with
  | nil => trivial
  | cons b bs ih =>
      have hpair := List.pairwise_cons.mp hp
      exact ⟨hpos b (by simp), ih b.t hpair.1 hpair.2⟩

lemma sums_ofFn {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)} (m : ℕ) :
    ∀ f : Fin m → PathFaceBlock (L := L) P w,
      blockBudgetSum (List.ofFn f) = ∑ i, (f i).B ∧
      blockRemovedLength (List.ofFn f) = ∑ i, ((f i).t - (f i).s) := by
  induction m with
  | zero =>
      intro f
      simp [blockBudgetSum, blockRemovedLength]
  | succ m ih =>
      intro f
      have h := ih (fun i => f i.succ)
      constructor
      · simpa only [List.ofFn_succ, blockBudgetSum, Fin.sum_univ_succ] using
          congrArg (fun z => (f 0).B + z) h.1
      · simpa only [List.ofFn_succ, blockRemovedLength, Fin.sum_univ_succ] using
          congrArg (fun z => ((f 0).t - (f 0).s) + z) h.2

end HirschDamagePublic

/-- Public-vocabulary exact repair theorem. Only steps outside the ordered
half-open intervals must survive. Interior points and steps are unrestricted. -/
theorem solution
    {d m L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (s t B : Fin m → ℕ)
    (F : Fin m → Set (EuclideanSpace ℝ (Fin d)))
    (hst : ∀ i, s i ≤ t i) (htL : ∀ i, t i ≤ L)
    (horder : ∀ i j, i < j → t i ≤ s j)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hD : ∀ i, DiamLE (F i) (B i))
    (hends : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hin : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hsurvive : ∀ j, j < L → (∀ i, j < s i ∨ t i ≤ j) →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (L - (∑ i, (t i - s i)) + (∑ i, B i)) = w L ∧
      ∀ j < L - (∑ i, (t i - s i)) + (∑ i, B i),
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  classical
  let f : Fin m → PathFaceBlock (L := L) P w := fun i =>
    { s := s i, t := t i, B := B i, F := F i
      hst := hst i, htL := htL i, hF := hF i, hFD := hD i
      hsP := (hends i).1, htP := (hends i).2
      hsF := (hin i).1, htF := (hin i).2 }
  have hord : BlocksOrderedFrom 0 (List.ofFn f) := by
    apply HirschDamagePublic.ordered_of_pairwise
    · intro b _
      exact Nat.zero_le b.s
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      exact horder i j hij
  have hs : ∀ j, j < L → StepOutsideBlocks (List.ofFn f) j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
    intro j hj hout
    apply hsurvive j hj
    intro i
    exact hout (f i) ((List.mem_ofFn' f (f i)).mpr ⟨i, rfl⟩)
  have h := splice_ordered_face_blocks_of_surviving_steps_exact
    P (w 0) (w L) w rfl rfl (List.ofFn f) hord hs
  have hsum := HirschDamagePublic.sums_ofFn m f
  rw [hsum.1, hsum.2] at h
  simpa only [f] using h

end

#print axioms solution
