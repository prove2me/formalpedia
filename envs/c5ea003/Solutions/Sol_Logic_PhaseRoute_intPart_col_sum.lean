-- Prove2me | solution 1 for Logic.PhaseRoute.intPart_col_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T12:14:18.256051+00:00
-- url     : https://prove2.me/submissions/5059c4a3-d9ac-425a-a3ea-0af90185126b

/-
# `Logic.PhaseRoute.avg_additive`
Target `37c1e942` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle built, closure screens CLEAN. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries FOUR):
    ∀ {α β} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (u : α → ℝ) (v : β → ℝ),
      avg (additive u v) = avg u + avg v

DEFINITIONS (read from source):
    avg (f : ι → ℝ)      = (∑ i, f i) / (Fintype.card ι : ℝ)     [LeastSquares:41]
    additive u v         = fun x : α × β => u x.1 + v x.2         [Alignment:79]

MATHS. `additive u v` splits as a first-coordinate lift plus a second-coordinate lift, `avg` is
additive over `Finset.sum`, and each lift averages to the average of its own factor — which is
`avg_comp_fst` and `avg_comp_snd`. Those are separate targets in this bundle, so they are RE-DERIVED
INLINE here: importing them from `Theorems/` would force the reduction path and an axiom audit.

    ∑_{(a,b)} (u a + v b) = ∑_{(a,b)} u a + ∑_{(a,b)} v b = |β|·∑u + |α|·∑v
    avg = (|β|·∑u + |α|·∑v) / (|α|·|β|) = ∑u/|α| + ∑v/|β|

Both nonemptiness hypotheses are load-bearing: each cancellation needs its own cardinality nonzero.

PROBED, NOT GUESSED — `#check`ed in a probe, with four of five step-examples compiling:
  * `Fintype.sum_prod_type (f : α₁ × α₂ → γ) : ∑ x, f x = ∑ x, ∑ y, f (x, y)`
  * `Finset.sum_const (b) : ∑ _x ∈ s, b = #s • b`
  * `Fintype.card_prod (α β) : card (α × β) = card α * card β`
  * `rw [avg]` unfolds directly; the one gap found was `Finset.sum_mul`.
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteANOVA

set_option autoImplicit false
set_option maxHeartbeats 400000

open Logic.PhaseRoute Finset

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α × β → ℝ) (b : β) :
    ∑ a, intPart f (a, b) = 0 := by
  have hA : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hT : (∑ a : α, ∑ b' : β, f (a, b')) = ∑ x : α × β, f x :=
    (Fintype.sum_prod_type f).symm
  have key : ∀ a : α, intPart f (a, b)
      = f (a, b) - (∑ b' : β, f (a, b')) / (Fintype.card β : ℝ)
        - (∑ a' : α, f (a', b)) / (Fintype.card α : ℝ)
        + (∑ x : α × β, f x) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
    intro a
    simp only [intPart, addPart, additive, rowMean, colMean, avg, Fintype.card_prod, Nat.cast_mul]
    ring
  have s2 : (∑ a : α, (∑ b' : β, f (a, b')) / (Fintype.card β : ℝ))
      = (∑ x : α × β, f x) / (Fintype.card β : ℝ) := by
    rw [← Finset.sum_div, hT]
  have s3 : (∑ _a : α, (∑ a' : α, f (a', b)) / (Fintype.card α : ℝ))
      = (Fintype.card α : ℝ) * ((∑ a' : α, f (a', b)) / (Fintype.card α : ℝ)) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have s4 : (∑ _a : α, (∑ x : α × β, f x) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))
      = (Fintype.card α : ℝ)
          * ((∑ x : α × β, f x) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, s2, s3, s4]
  field_simp
  ring


