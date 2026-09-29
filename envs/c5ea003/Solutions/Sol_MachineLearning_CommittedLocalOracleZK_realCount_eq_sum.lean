-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZK.realCount_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:56:49.826524+00:00
-- url     : https://prove2.me/submissions/82281213-c242-47f4-a996-645f028d3db1

/-
# `MachineLearning.CommittedLocalOracleZK.realCount_eq_sum`
Target `c0d90cc4` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (NINE instances; siblings differ, so
none of this is carried over):
    ∀ {I A C O Rc Rv P} [DecidableEq I] [Fintype I] [Fintype Rc] [Fintype Rv] [Fintype P]
      [DecidableEq A] [DecidableEq C] [DecidableEq O] [DecidableEq Rv]
      (Pr : CommittedOracle I A C O Rc Rv P) (c : C) (r₀ : Rv) (t : I → Option A) (o : O), …
No `S`, no `Fintype S`. `Pr c r₀ t o` all EXPLICIT.

DEFINITIONS:
    realTranscript Pr p ρ r = (Pr.com (Pr.proof p) ρ, r,
                               restrictTo (Pr.Q r) (Pr.proof p), Pr.openInfo (Pr.proof p) ρ (Pr.Q r))
    realCount Pr τ = (univ.filter fun x : P × Rc × Rv => realTranscript Pr x.1 x.2.1 x.2.2 = τ).card
    fiberCount Pr u T c o = (univ.filter fun ρ => Pr.com u ρ = c ∧ Pr.openInfo u ρ T = o).card

MATHS. Count the triples `(p, ρ, r)` fibrewise over `p`. Transcript equality forces `r = r₀` from the
SECOND component; the remaining three conditions split cleanly:
  * `restrictTo (Pr.Q r₀) (Pr.proof p) = t` — does NOT mention `ρ`, so it is constant on the fibre,
    which is exactly why an `if` appears rather than a finer sum;
  * `Pr.com (Pr.proof p) ρ = c ∧ Pr.openInfo (Pr.proof p) ρ (Pr.Q r₀) = o` — precisely `fiberCount`'s
    predicate.
So the fibre is EMPTY when the restriction misses `t`, and otherwise is in bijection with the `ρ`s
counted by `fiberCount`, via `x ↦ x.2.1` and `ρ ↦ (p, ρ, r₀)`.

PROBED, NOT GUESSED — every statement below was READ from Mathlib source:
  * `Finset.card_eq_sum_card_fiberwise (H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b}`
    — Basic.lean:980; the same lemma that carried my accepted `cnt_comp`. With `t := univ` the
    `MapsTo` obligation is `fun _ _ => mem_univ _`.
  * `Finset.card_nbij' (i) (j) (hi : MapsTo i s t) (hj : MapsTo j t s)
       (left_inv : LeftInvOn j i s) (right_inv : RightInvOn j i t) : #s = #t` — Card.lean:403.
    SIX arguments, and the inverse conditions are `Set.LeftInvOn`/`Set.RightInvOn`, not plain `∀`.
  * `Finset.card_eq_zero : #s = 0 ↔ s = ∅` (Card.lean:76) and
    `Finset.filter_eq_empty_iff : s.filter p = ∅ ↔ ∀ ⦃x⦄, x ∈ s → ¬ p x` (Filter.lean:159) —
    note the STRICT-implicit binder on `x`.
  * `Prod.mk_inj : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂` (Prod/Basic.lean:68) — this is what
    extracts `r = r₀` from the transcript's second component.
-/
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MachineLearning.CommittedLocalOracleZK Finset

open MachineLearning.CommittedLocalOracleZK in
/-- **The target, verbatim.** -/
theorem solution {I A C O Rc Rv P : Type*} [DecidableEq I] [Fintype I] [Fintype Rc] [Fintype Rv]
    [Fintype P] [DecidableEq A] [DecidableEq C] [DecidableEq O] [DecidableEq Rv]
    (Pr : CommittedOracle I A C O Rc Rv P) (c : C) (r₀ : Rv) (t : I → Option A) (o : O) :
    realCount Pr (c, r₀, t, o)
      = ∑ p, if restrictTo (Pr.Q r₀) (Pr.proof p) = t
             then fiberCount Pr (Pr.proof p) (Pr.Q r₀) c o else 0 := by
  classical
  show (Finset.univ.filter fun x : P × Rc × Rv =>
          realTranscript Pr x.1 x.2.1 x.2.2 = (c, r₀, t, o)).card = _
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun x : P × Rc × Rv => x.1) (t := (Finset.univ : Finset P))
        (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl ?_
  intro p _
  -- membership in the fibre, unfolded once and reused by both branches
  have hmem : ∀ x : P × Rc × Rv,
      (x ∈ (Finset.univ.filter fun y : P × Rc × Rv =>
              realTranscript Pr y.1 y.2.1 y.2.2 = (c, r₀, t, o)).filter (fun y => y.1 = p))
        ↔ (x.1 = p ∧ x.2.2 = r₀ ∧ restrictTo (Pr.Q r₀) (Pr.proof p) = t ∧
            Pr.com (Pr.proof p) x.2.1 = c ∧ Pr.openInfo (Pr.proof p) x.2.1 (Pr.Q r₀) = o) := by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, realTranscript, Prod.mk_inj]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
      subst h5; subst h2
      exact ⟨rfl, rfl, h3, h1, h4⟩
    · rintro ⟨h5, h2, h3, h1, h4⟩
      subst h5; subst h2
      exact ⟨⟨h1, rfl, h3, h4⟩, rfl⟩
  by_cases hrest : restrictTo (Pr.Q r₀) (Pr.proof p) = t
  · rw [if_pos hrest]
    show _ = (Finset.univ.filter fun ρ =>
                Pr.com (Pr.proof p) ρ = c ∧ Pr.openInfo (Pr.proof p) ρ (Pr.Q r₀) = o).card
    refine Finset.card_nbij' (fun x => x.2.1) (fun ρ => (p, ρ, r₀)) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, hmem] at hx
      simpa using ⟨hx.2.2.2.1, hx.2.2.2.2⟩
    · intro ρ hρ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hρ
      rw [Finset.mem_coe, hmem]
      exact ⟨rfl, rfl, hrest, hρ.1, hρ.2⟩
    · intro x hx
      rw [Finset.mem_coe, hmem] at hx
      obtain ⟨h1, h2, -, -, -⟩ := hx
      exact Prod.ext h1.symm (Prod.ext rfl h2.symm)
    · intro ρ _
      rfl
  · rw [if_neg hrest, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    intro hx1
    apply hrest
    have := hx
    simp only [realTranscript, Prod.mk_inj] at this
    obtain ⟨-, h2, h3, -⟩ := this
    subst hx1
    rw [← h2]
    exact h3
