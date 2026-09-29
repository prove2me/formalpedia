-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZK.simCount_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T10:00:28.486519+00:00
-- url     : https://prove2.me/submissions/c7840157-1a2a-40df-8e8e-2b14b6836e61

/-
# `MachineLearning.CommittedLocalOracleZK.simCount_eq_sum`
Target `b93489b8` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN. Gift: **SAFE**.

BINDERS — from THIS target's own WA, verbatim. Note it is NOT the sibling's list:
    ∀ {I A C O Rc Rv P S} [DecidableEq I] [Fintype I] [Fintype Rc] [Fintype Rv] [Fintype S]
      [DecidableEq A] [DecidableEq C] [DecidableEq O] [DecidableEq Rv]
      (Pr : CommittedOracle I A C O Rc Rv P) (sim : Rv → S → I → A)
      (c : C) (r₀ : Rv) (t : I → Option A) (o : O), …
`S` is bound and `[Fintype S]` appears where `realCount_eq_sum` has `[Fintype P]` — because
`simCount` mentions the simulator's randomness and never the prover's. `P` survives only as a type
argument of `CommittedOracle`, with NO `Fintype P`. Carrying the sibling's list across would compile
and be rejected on type; that is how five earlier submissions here failed.

DEFINITIONS:
    simTranscript Pr sim s ρ r = (Pr.com (sim r s) ρ, r,
                                  restrictTo (Pr.Q r) (sim r s), Pr.openInfo (sim r s) ρ (Pr.Q r))
    simCount Pr sim τ = (univ.filter fun x : S × Rc × Rv => simTranscript Pr sim x.1 x.2.1 x.2.2 = τ).card

MATHS — the mirror of `realCount_eq_sum`, for the same structural reason. Transcript equality forces
`r = r₀` from the SECOND component. Of what remains, `restrictTo (Pr.Q r₀) (sim r₀ s) = t` mentions
only `s`, so it is constant on the fibre above `s` — hence an `if` rather than a finer sum — and
`Pr.com (sim r₀ s) ρ = c ∧ Pr.openInfo (sim r₀ s) ρ (Pr.Q r₀) = o` is exactly `fiberCount`'s
predicate. Each fibre is therefore empty, or in bijection with the `ρ`s via `x ↦ x.2.1` and
`ρ ↦ (s, ρ, r₀)`.

PROBED, NOT GUESSED — all READ from Mathlib source:
  * `Finset.card_eq_sum_card_fiberwise (H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b}`
    (Basic.lean:980); with `t := univ` the obligation is `fun _ _ => mem_univ _`.
  * `Finset.card_nbij' (i) (j) (hi : MapsTo i s t) (hj : MapsTo j t s)
       (left_inv : LeftInvOn j i s) (right_inv : RightInvOn j i t) : #s = #t` (Card.lean:403) — SIX
    arguments, inverses as `Set.LeftInvOn`/`Set.RightInvOn`.
  * `Finset.card_eq_zero : #s = 0 ↔ s = ∅` (Card.lean:76);
    `Finset.filter_eq_empty_iff : s.filter p = ∅ ↔ ∀ ⦃x⦄, x ∈ s → ¬ p x` (Filter.lean:159) — STRICT
    implicit binder.
  * `Prod.mk_inj : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂` (Prod/Basic.lean:68) — extracts `r = r₀`.
-/
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MachineLearning.CommittedLocalOracleZK Finset

open MachineLearning.CommittedLocalOracleZK in
/-- **The target, verbatim.** -/
theorem solution {I A C O Rc Rv P S : Type*} [DecidableEq I] [Fintype I] [Fintype Rc] [Fintype Rv]
    [Fintype S] [DecidableEq A] [DecidableEq C] [DecidableEq O] [DecidableEq Rv]
    (Pr : CommittedOracle I A C O Rc Rv P) (sim : Rv → S → I → A)
    (c : C) (r₀ : Rv) (t : I → Option A) (o : O) :
    simCount Pr sim (c, r₀, t, o)
      = ∑ s, if restrictTo (Pr.Q r₀) (sim r₀ s) = t
             then fiberCount Pr (sim r₀ s) (Pr.Q r₀) c o else 0 := by
  classical
  show (Finset.univ.filter fun x : S × Rc × Rv =>
          simTranscript Pr sim x.1 x.2.1 x.2.2 = (c, r₀, t, o)).card = _
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun x : S × Rc × Rv => x.1) (t := (Finset.univ : Finset S))
        (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl ?_
  intro s _
  have hmem : ∀ x : S × Rc × Rv,
      (x ∈ (Finset.univ.filter fun y : S × Rc × Rv =>
              simTranscript Pr sim y.1 y.2.1 y.2.2 = (c, r₀, t, o)).filter (fun y => y.1 = s))
        ↔ (x.1 = s ∧ x.2.2 = r₀ ∧ restrictTo (Pr.Q r₀) (sim r₀ s) = t ∧
            Pr.com (sim r₀ s) x.2.1 = c ∧ Pr.openInfo (sim r₀ s) x.2.1 (Pr.Q r₀) = o) := by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, simTranscript, Prod.mk_inj]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
      subst h5; subst h2
      exact ⟨rfl, rfl, h3, h1, h4⟩
    · rintro ⟨h5, h2, h3, h1, h4⟩
      subst h5; subst h2
      exact ⟨⟨h1, rfl, h3, h4⟩, rfl⟩
  by_cases hrest : restrictTo (Pr.Q r₀) (sim r₀ s) = t
  · rw [if_pos hrest]
    show _ = (Finset.univ.filter fun ρ =>
                Pr.com (sim r₀ s) ρ = c ∧ Pr.openInfo (sim r₀ s) ρ (Pr.Q r₀) = o).card
    refine Finset.card_nbij' (fun x => x.2.1) (fun ρ => (s, ρ, r₀)) ?_ ?_ ?_ ?_
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
    have hcopy := hx
    simp only [simTranscript, Prod.mk_inj] at hcopy
    obtain ⟨-, h2, h3, -⟩ := hcopy
    subst hx1
    rw [← h2]
    exact h3
