-- Prove2me | solution 1 for RLHF.schedule_collapse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:17:42.373916+00:00
-- url     : https://prove2.me/submissions/42319bc9-c5e3-49e1-a472-f7c201173dff

-- Sol generated from NumberTheory/RLHFScheduleCollapse.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFRewardIdentifiability
import Definitions.Def_NumberTheory_RLHFScheduleCollapse
import Theorems.Thm_RLHF_gibbsPolicy_isPosDist
import Theorems.Thm_RLHF_gibbs_compose

/-!
# Temperature schedules collapse: iterated RLHF is single-step RLHF

This file settles Conjecture 4 of `FUTURE_DIRECTIONS.md`.  `RLHF.gibbs_compose` shows that
two alignment steps *at the same temperature* add their reward models.  A real training
pipeline, however, runs a **schedule**: step `i` uses its own KL coefficient `β i` and its
own reward `r i`.  We show that the whole schedule collapses:

* `RLHF.gibbsPolicy_rescale` — only the ratio `r / β` matters, so a step at temperature `β'`
  is a step at temperature `β` with the rescaled reward `(β/β') r`.
* `RLHF.gibbs_schedule_two` — a two-step schedule equals one step with reward
  `(β/β₁) r₁ + (β/β₂) r₂`.
* `RLHF.runSchedule` and `RLHF.schedule_collapse` — an arbitrary finite schedule, folded left
  over a list of (temperature, reward) pairs, equals a single RLHF step at any chosen
  temperature `β` with reward `∑ᵢ (β/βᵢ) rᵢ`.
* `RLHF.schedule_reachable_in_one_step` — consequently no multi-step schedule can reach a
  policy that is unreachable in one step: the reachable set is exactly the orbit of the
  one-step map, so iterated RLHF adds no expressive power (only optimization dynamics).
* `RLHF.zeta_schedule_collapse` — arithmetic payoff: for Dirichlet rewards on a smooth-number
  response space, a schedule with sharpnesses `s₁, s₂` at *arbitrary* temperatures produces
  the truncated zeta policy of exponent `s₁ + s₂`, independently of the schedule.  The
  alignment schedule acts on Dirichlet exponents by addition, i.e. by multiplication of the
  associated Dirichlet series.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Only the ratio reward/temperature matters -/

omit [Nonempty Ω] in
/-- **Temperature–reward rescaling.**  A step at temperature `β'` with reward `r` is exactly
a step at temperature `β` with the rescaled reward `(β/β') r`. -/
theorem gibbsPolicy_rescale {β β' : ℝ} (hβ : β ≠ 0) (hβ' : β' ≠ 0) (r p : Ω → ℝ) :
    gibbsPolicy β (fun y => (β / β') * r y) p = gibbsPolicy β' r p := by
  have hexp : ∀ y, ((β / β') * r y) / β = r y / β' := by
    intro y; field_simp
  unfold gibbsPolicy partition
  simp only [hexp]

omit [Nonempty Ω] in
/-- A zero reward model leaves the reference policy unchanged. -/
theorem gibbsPolicy_zero {β : ℝ} {p : Ω → ℝ} (hp : IsPosDist p) :
    gibbsPolicy β (fun _ => (0 : ℝ)) p = p := by
  have hZ : partition β (fun _ => (0 : ℝ)) p = 1 := by
    unfold partition
    simpa using hp.2
  funext y
  unfold gibbsPolicy
  rw [hZ]
  simp


/-! ## 2. Arbitrary finite schedules -/



omit [Nonempty Ω] in
@[simp] theorem runSchedule_cons (p : Ω → ℝ) (br : ℝ × (Ω → ℝ)) (L : List (ℝ × (Ω → ℝ))) :
    runSchedule p (br :: L) = runSchedule (gibbsPolicy br.1 br.2 p) L := rfl



/-! ## 3. Arithmetic corollary: Dirichlet exponents add along any schedule -/

variable {A B : ℕ}




open RLHF in
theorem solution{β : ℝ} (hβ : β ≠ 0) :
    ∀ (L : List (ℝ × (Ω → ℝ))) (p : Ω → ℝ), IsPosDist p → (∀ br ∈ L, br.1 ≠ 0) →
      runSchedule p L
        = gibbsPolicy β (fun y => (L.map (fun br => (β / br.1) * br.2 y)).sum) p := by
  intro L
  induction L with
  | nil =>
    intro p hp _
    simpa using (gibbsPolicy_zero (β := β) hp).symm
  | cons br L ih =>
    intro p hp hne
    have hbr : br.1 ≠ 0 := hne br (List.mem_cons_self ..)
    have hpq : IsPosDist (gibbsPolicy β (fun y => (β / br.1) * br.2 y) p) :=
      gibbsPolicy_isPosDist hp
    rw [runSchedule_cons, ← gibbsPolicy_rescale hβ hbr br.2 p,
      ih _ hpq (fun c hc => hne c (List.mem_cons_of_mem _ hc)),
      gibbs_compose (r₁ := fun y => (β / br.1) * br.2 y)
        (r₂ := fun y => (L.map (fun c => (β / c.1) * c.2 y)).sum) hp]
    simp
