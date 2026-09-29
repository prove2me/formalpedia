-- Prove2me | solution 1 for TraceBattery.cnt_comp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T08:51:06.300332+00:00
-- url     : https://prove2.me/submissions/765c01d9-9066-43cf-afe7-1706ce4bac56

/-
# `TraceBattery.cnt_comp`
Target `a36a0f0d` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN, BUILT. Gift check (corrected logic): **SAFE**.

BINDERS — history `CE,CE`; every failure on this bundle read `unknown namespace TraceBattery.Entropy`
(`Entropy` is a SECTION, not a namespace). Declared INLINE: `(f : Ω → α) (g : α → β) (b : β)` over
`variable {Ω : Type*} [Fintype Ω] {α β : Type*}` (bundle line 46). Gate is the sole authority.

MATHS. Retained definitions:

    fib f a = univ.filter (fun x => f x = a)
    cnt f a = (fib f a).card
    img f   = univ.image f

Goal: `cnt (g ∘ f) b = ∑ a ∈ (img f).filter (g · = b), cnt f a`, i.e. the individuals whose composed
reading is `b`, counted by partitioning them over the intermediate reading `a = f x`.

That is `Finset.card_eq_sum_card_fiberwise` (Algebra/BigOperators/Group/Finset/Basic.lean:980):

    [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M}
      (H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b}

with `s := univ.filter (fun x => g (f x) = b)`, map `f`, `t := (img f).filter (g · = b)`.

TWO OBLIGATIONS:
  * `MapsTo` — for `x` with `g (f x) = b`: `f x ∈ img f` (it is a value of `f`), and `g (f x) = b`.
  * the summand must match `cnt f a`, i.e. `{x ∈ s | f x = a}` must equal `fib f a`. It does: if
    `f x = a` and `a` satisfies `g a = b`, then `g (f x) = b` follows, so membership of `s` is
    automatic and the extra condition is redundant. THIS is the step I have not verified — flagged.
-/
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TraceBattery Finset

section Probes
#check @Finset.card_eq_sum_card_fiberwise
#check @Finset.mem_image_of_mem
#check @Finset.filter_congr

-- (A) the redundancy step in isolation: given `g a = b`, the `s`-condition follows from `f x = a`
open Classical in
example {Ω : Type*} [Fintype Ω] {α β : Type*} (f : Ω → α) (g : α → β) (b : β)
    (a : α) (hga : g a = b) :
    Finset.univ.filter (fun x => (g (f x) = b) ∧ f x = a)
      = Finset.univ.filter (fun x => f x = a) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rw [h, hga], h⟩
end Probes

open Classical TraceBattery in
/-- **The target, verbatim.** -/
theorem solution {Ω : Type*} [Fintype Ω] {α β : Type*} (f : Ω → α) (g : α → β) (b : β) :
    cnt (g ∘ f) b = ∑ a ∈ (img f).filter (fun a => g a = b), cnt f a := by
  classical
  -- unfold both sides to filters of `univ`
  show (Finset.univ.filter (fun x => (g ∘ f) x = b)).card
      = ∑ a ∈ (img f).filter (fun a => g a = b), (Finset.univ.filter (fun x => f x = a)).card
  -- partition the left side over the intermediate reading
  have hmaps : (↑(Finset.univ.filter (fun x => (g ∘ f) x = b)) : Set Ω).MapsTo f
      ((img f).filter (fun a => g a = b)) := by
    intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx
    refine Finset.mem_filter.mpr ⟨?_, hx⟩
    show f x ∈ Finset.image f Finset.univ
    exact Finset.mem_image_of_mem f (Finset.mem_univ x)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  -- each fibre-within-the-slice is just the fibre: the slice condition is implied
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hga : g a = b := (Finset.mem_filter.mp ha).2
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rw [h, hga], h⟩
