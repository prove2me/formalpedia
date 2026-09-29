-- Prove2me | solution 1 for TraceBattery.H_pos_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:04:48.554496+00:00
-- url     : https://prove2.me/submissions/0e73f050-6da0-4d10-a3fb-4117a935cfd4

/-
# `TraceBattery.H_pos_of_ne`
Target `5b20b51b` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN, BUILT. Gift check (corrected logic): **SAFE**.

BINDERS — FIRST ATTEMPT REJECTED BY THE GATE (binder-structure mismatch, 9 binders each,
positions 3/4 transposed). The mirror is the authority: section variables come first in their
DECLARED order `{Ω} [Fintype Ω] {α}`, THEN the theorem's own `[Nonempty Ω]`. I had put
`[Nonempty Ω]` before `{α}`. `β` is in the variable line but unused, so Lean omits it.
Declared INLINE: `[Nonempty Ω] {f : Ω → α} {x y : Ω} (hxy : f x ≠ f y)` over
`variable {Ω : Type*} [Fintype Ω] {α β : Type*}` (bundle line 46). Gate is the sole authority.

MATHS.  H f = ∑ a ∈ img f, (cnt f a / N) * log (N / cnt f a),  N = Fintype.card Ω.
  * every term is ≥ 0: on the image `0 < cnt f a ≤ N`, so `N / cnt ≥ 1`, `log ≥ 0`, factor ≥ 0;
  * the term at `a = f x` is > 0: `y` lies outside the fibre over `f x` (since `f y ≠ f x`), so
    `cnt f (f x) < N` STRICTLY, giving `N / cnt > 1` and `log > 0`.
  A non-negative sum with one strictly positive term is positive.

NOTE ON REUSE. `cnt_pos_of_mem_img` and `self_mem_img` are theorems I have had ACCEPTED, but
importing from `Theorems/` would make this depend on that tree and force an axiom audit — so both
are re-derived inline (four lines each).

PROBED, NOT GUESSED:
  * `Finset.sum_pos' (h : ∀ i ∈ s, 0 ≤ g i) (hf : ∃ i ∈ s, 0 < g i) : 0 < ∑ i ∈ s, g i`
    — confirmed by five call sites; shape `(fun i _ ↦ …) ⟨w, …⟩`.
  * `Finset.card_lt_card (h : s ⊂ t) : #s < #t` (Card.lean:307) — declared `nonrec lemma`, which is
    why a `^(theorem|lemma)` grep found nothing. Seventh false-negative mechanism today.
  * `Finset.filter_ssubset : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬ p x` (Filter.lean:133)
  * `Finset.card_filter_le`, `Real.log_pos (1 < x)`, `Real.log_nonneg (1 ≤ x)`, `Fintype.card_pos`
-/
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TraceBattery Finset

section Probes
#check @Finset.sum_pos'
#check @Finset.card_lt_card
#check @Finset.filter_ssubset
#check @Real.log_pos
#check @Real.log_nonneg

-- (A) a fibre missing a known point is a PROPER subset of univ, hence strictly smaller
example {Ω : Type*} [Fintype Ω] (p : Ω → Prop) [DecidablePred p] (y : Ω) (hy : ¬ p y) :
    (Finset.univ.filter p).card < Fintype.card Ω := by
  have hss : Finset.univ.filter p ⊂ Finset.univ :=
    Finset.filter_ssubset.mpr ⟨y, Finset.mem_univ y, hy⟩
  simpa using Finset.card_lt_card hss
end Probes

open TraceBattery in
/-- **The target, verbatim.** -/
theorem solution {Ω : Type*} [Fintype Ω] {α : Type*} [Nonempty Ω] {f : Ω → α} {x y : Ω}
    (hxy : f x ≠ f y) : 0 < H f := by
  classical
  have hNpos : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  -- membership in the image (re-derived: this is `self_mem_img`)
  have hmem : ∀ z : Ω, f z ∈ img f := by
    intro z
    show f z ∈ Finset.image f Finset.univ
    exact Finset.mem_image_of_mem f (Finset.mem_univ z)
  -- positivity of counts on the image (re-derived: this is `cnt_pos_of_mem_img`)
  have hcpos : ∀ a ∈ img f, 0 < cnt f a := by
    intro a ha
    have ha' : a ∈ Finset.image f Finset.univ := ha
    rcases Finset.mem_image.mp ha' with ⟨z, -, hz⟩
    have : z ∈ fib f a := by
      show z ∈ Finset.univ.filter (fun w => f w = a)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩
    show 0 < (fib f a).card
    exact Finset.card_pos.mpr ⟨z, this⟩
  -- counts never exceed the population
  have hcle : ∀ a : α, cnt f a ≤ Fintype.card Ω := by
    intro a
    show (Finset.univ.filter (fun w => f w = a)).card ≤ Fintype.card Ω
    simpa using Finset.card_filter_le Finset.univ (fun w => f w = a)
  -- every term of H is non-negative
  have hterm : ∀ a ∈ img f,
      0 ≤ (cnt f a / (Fintype.card Ω : ℝ)) * Real.log ((Fintype.card Ω : ℝ) / cnt f a) := by
    intro a ha
    have h1 : (0:ℝ) < cnt f a := by exact_mod_cast hcpos a ha
    have h2 : (cnt f a : ℝ) ≤ (Fintype.card Ω : ℝ) := by exact_mod_cast hcle a
    have hlog : 0 ≤ Real.log ((Fintype.card Ω : ℝ) / cnt f a) :=
      Real.log_nonneg ((one_le_div h1).mpr h2)
    exact mul_nonneg (div_nonneg h1.le hNpos.le) hlog
  -- the term at `f x` is strictly positive: `y` is outside that fibre
  have hstrict : cnt f (f x) < Fintype.card Ω := by
    have hy : ¬ (f y = f x) := fun h => hxy h.symm
    have hss : Finset.univ.filter (fun w => f w = f x) ⊂ Finset.univ :=
      Finset.filter_ssubset.mpr ⟨y, Finset.mem_univ y, hy⟩
    show (Finset.univ.filter (fun w => f w = f x)).card < Fintype.card Ω
    simpa using Finset.card_lt_card hss
  have hpos : 0 < (cnt f (f x) / (Fintype.card Ω : ℝ))
      * Real.log ((Fintype.card Ω : ℝ) / cnt f (f x)) := by
    have h1 : (0:ℝ) < cnt f (f x) := by exact_mod_cast hcpos _ (hmem x)
    have h2 : (cnt f (f x) : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hstrict
    have hlog : 0 < Real.log ((Fintype.card Ω : ℝ) / cnt f (f x)) :=
      Real.log_pos ((one_lt_div h1).mpr h2)
    exact mul_pos (div_pos h1 hNpos) hlog
  show 0 < ∑ a ∈ img f, (cnt f a / (Fintype.card Ω : ℝ))
      * Real.log ((Fintype.card Ω : ℝ) / cnt f a)
  exact Finset.sum_pos' hterm ⟨f x, hmem x, hpos⟩
