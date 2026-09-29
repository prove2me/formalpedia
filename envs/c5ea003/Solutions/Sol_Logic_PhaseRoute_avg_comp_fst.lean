-- Prove2me | solution 1 for Logic.PhaseRoute.avg_comp_fst
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:36:59.005047+00:00
-- url     : https://prove2.me/submissions/0728b713-f561-4a9e-ae7b-de519b057097

/-
# `Logic.PhaseRoute.avg_comp_fst`
Target `7b288671` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle built, closure screens CLEAN. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries FOUR):
    ∀ {α β} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (f : α → ℝ),
      (avg fun x => f x.1) = avg f
Note `[Nonempty α] [Nonempty β]` ARE required, even though `#check @avg` shows
`{ι} → [Fintype ι] → (ι → ℝ) → ℝ` — `avg` itself does not need nonemptiness. The instances come from
`section Product`'s variable line and are part of the expected signature, so they are taken verbatim
rather than trimmed to what `avg` appears to use.

DEFINITIONS (read from Def_Logic_PhaseRouteLeastSquares:41):
    avg (f : ι → ℝ) = (∑ i, f i) / (Fintype.card ι : ℝ)

MATHS. Averaging a function of the first coordinate over the product ignores the second:
    ∑_{(a,b)} f a = ∑_a ∑_b f a = ∑_a (|β| • f a) = |β| · ∑_a f a
and `|α × β| = |α|·|β|`, so the `|β|` cancels. Nonemptiness of `β` is what makes that cancellation
legitimate — with `β` empty both sides would be `0/0`.

PROBED, NOT GUESSED — every lemma below was `#check`ed in a probe, and four of five step-examples
compiled:
  * `Fintype.sum_prod_type (f : α₁ × α₂ → γ) : ∑ x, f x = ∑ x, ∑ y, f (x, y)`
  * `Finset.sum_const (b) : ∑ _x ∈ s, b = #s • b`
  * `Fintype.card_prod (α β) : card (α × β) = card α * card β`
  * `rw [avg]` unfolds the definition directly (it is a plain def, not well-founded).
  * the one step that did NOT close was `∑ x, f x * c = (∑ a, f a) * c`, which is `Finset.sum_mul`.
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment

set_option autoImplicit false
set_option maxHeartbeats 400000

open Logic.PhaseRoute Finset

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (f : α → ℝ) :
    avg (fun x : α × β => f x.1) = avg f := by
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card β := Fintype.card_pos
    positivity
  have hα : (Fintype.card α : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    positivity
  have hnum : (∑ x : α × β, f x.1) = (Fintype.card β : ℝ) * ∑ a, f a := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, Finset.sum_mul, mul_comm]
  rw [avg, avg, hnum, Fintype.card_prod, Nat.cast_mul]
  field_simp
