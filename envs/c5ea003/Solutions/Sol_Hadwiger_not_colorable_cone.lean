-- Prove2me | solution 1 for Hadwiger.not_colorable_cone
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:53:10.853097+00:00
-- url     : https://prove2.me/submissions/3ea3769b-d6a6-4c43-96f0-7e4e1b874043

import Mathlib
import Definitions.Def_Probability_HadwigerMonotone
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QuickCone
open Hadwiger SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

@[simp] theorem cone_adj_inl {a b : V} : (cone G).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b :=
  Iff.rfl

@[simp] theorem cone_adj_apex_right {a : V} {u : Unit} : (cone G).Adj (Sum.inl a) (Sum.inr u) :=
  trivial

@[simp] theorem cone_adj_apex_left {a : V} {u : Unit} : (cone G).Adj (Sum.inr u) (Sum.inl a) :=
  trivial

/-! ### The cone needs one more colour -/

/-- Deleting the colour `a` from `Fin (k+1)`. -/
private def quickDropColor (k : ℕ) (a : Fin (k + 1)) (hk : 0 < k) (c : Fin (k + 1)) : Fin k :=
  if h : c.val < a.val then ⟨c.val, by omega⟩ else ⟨c.val - 1, by omega⟩

private theorem quickDropColor_injOn {k : ℕ} {a : Fin (k + 1)} (hk : 0 < k) {c d : Fin (k + 1)}
    (hc : c ≠ a) (hd : d ≠ a) (h : quickDropColor k a hk c = quickDropColor k a hk d) : c = d := by
  have hc' : c.val ≠ a.val := fun hcon => hc (Fin.ext hcon)
  have hd' : d.val ≠ a.val := fun hcon => hd (Fin.ext hcon)
  have hcv := c.isLt
  have hdv := d.isLt
  unfold quickDropColor at h
  split_ifs at h with h1 h2 h2 <;>
    · have := congrArg Fin.val h
      simp at this
      exact Fin.ext (by omega)

/-- **The cone needs one more colour than `G`.** -/
theorem not_colorable_cone {k : ℕ} (h : ¬ G.Colorable k) : ¬ (cone G).Colorable (k + 1) := by
  rintro ⟨C⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `G` is not `0`-colourable, so it has a vertex, which is adjacent to the apex
    have : Nonempty V := by
      by_contra hcon
      exact h (colorable_zero_iff.mpr (not_nonempty_iff.mp hcon))
    obtain ⟨v⟩ := this
    have hne : C (Sum.inl v) ≠ C (Sum.inr ()) := C.valid cone_adj_apex_right
    have h1 := (C (Sum.inl v)).isLt
    have h2 := (C (Sum.inr ())).isLt
    exact hne (Fin.ext (by omega))
  · set a := C (Sum.inr ()) with ha
    have hne : ∀ v : V, C (Sum.inl v) ≠ a := fun v => C.valid cone_adj_apex_right
    refine h ⟨Coloring.mk (fun v => quickDropColor k a hk (C (Sum.inl v))) ?_⟩
    intro x y hxy hcon
    exact C.valid (cone_adj_inl.mpr hxy)
      (quickDropColor_injOn hk (hne x) (hne y) hcon)


end QuickCone
open Hadwiger SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
theorem solution {k : ℕ} (h : ¬ G.Colorable k) : ¬ (cone G).Colorable (k + 1) := by
  exact QuickCone.not_colorable_cone h
#print axioms solution
