-- Prove2me | solution 1 for TraceBattery.cnt_pos_of_mem_img
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T08:33:57.293529+00:00
-- url     : https://prove2.me/submissions/ec5cf249-4adb-44c9-bad6-6fa775759a62

/-
# `TraceBattery.cnt_pos_of_mem_img`
Target `4c38508f` (Open; re-read live immediately before submitting).

ORDINARY PROOF — same bundle as `b8cd4142`, screened CLEAN, BUILT. Gift check: **SAFE**.

BINDERS — history `CE,CE`, so no WA and no expected type. Declared INLINE:
`{f : Ω → α} {a : α} (ha : a ∈ img f)` over `variable {Ω : Type*} [Fintype Ω] {α β : Type*}`
(bundle line 46); `β` is unmentioned so Lean drops it. Gate is the sole authority.

WHAT THE CEs REVEAL. Every failed attempt on this bundle — all three targets — died with
`unknown namespace TraceBattery.Entropy`. `Entropy` is a **section**, not a namespace, so
`open TraceBattery.Entropy` cannot resolve. A bundle-shape mistake, not a mathematical one, and the
likeliest reason a bundle of near-one-liners has stayed untouched.

MATHS. The bundle retains everything:

    fib f a = univ.filter (fun x => f x = a)
    cnt f a = (fib f a).card
    img f   = univ.image f

`a ∈ img f` means `a ∈ univ.image f`, which yields a witness `x` with `f x = a`. That witness lies in
`fib f a`, so the fibre is non-empty, so its card is positive.

PROBED, NOT GUESSED:
  * `Finset.mem_image` : `b ∈ s.image f ↔ ∃ a ∈ s, f a = b`
  * `Finset.card_pos`  : `0 < s.card ↔ s.Nonempty`
  * `Finset.mem_filter`: membership in a filtered finset
-/
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy

set_option autoImplicit false
set_option maxHeartbeats 400000

open TraceBattery Finset


open TraceBattery in
/-- **The target, verbatim.** -/
theorem solution {Ω : Type*} [Fintype Ω] {α : Type*} {f : Ω → α} {a : α}
    (ha : a ∈ img f) : 0 < cnt f a := by
  classical
  -- unfold the image to expose the witness
  have ha' : a ∈ Finset.image f Finset.univ := ha
  rcases Finset.mem_image.mp ha' with ⟨x, -, hx⟩
  -- that witness lies in the fibre over `a`
  have hmem : x ∈ fib f a := by
    show x ∈ Finset.univ.filter (fun y => f y = a)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
  show 0 < (fib f a).card
  exact Finset.card_pos.mpr ⟨x, hmem⟩
