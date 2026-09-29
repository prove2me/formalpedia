-- Prove2me | solution 1 for TangledSoundness.transGen_iterate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:44:16.204358+00:00
-- url     : https://prove2.me/submissions/fe0ab020-06be-496b-9f15-d9f84a189e9a

-- Sol generated from Logic/ProvabilityLogic/SelfConsistentSemantics.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_SelfConsistentSemantics
import Definitions.Def_Logic_ProvabilityLogic_SelfSoundSystems
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
/-
# Cycle 5: Every Finite Semantics of a Self-Consistent System Is Tangled

Cycle 4 built proof systems (`ModalSystem`) and showed that internal soundness and the
Löb axiom cannot coexist.  This cycle answers the remaining half of the mission
statement — *"tangled hierarchies are unavoidable in any system that can reason about
its own consistency"* — on the semantic side, and closes one step of the
`FUTURE_DIRECTIONS.md` degree-monoid conjecture.

## Main results

* `ModalSystem.serial_of_provesCon` — if a system proves its own consistency `¬□⊥`
  and a frame is sound for it, that frame is **serial**: no world is a dead end.
* `ModalSystem.isEmpty_of_provesCon_of_wf`, `glFrame_not_frameSound_of_provesCon` —
  hence no *nonempty* converse well-founded (GL) frame is sound for a system that
  asserts its own consistency.
* `finite_serial_has_cycle` and `ModalSystem.provesCon_finite_isTangled` —
  **the unavoidability theorem:** every *finite* frame sound for a system that proves
  its own consistency contains a cycle, so its reference graph (the transitive closure
  of accessibility) is tangled in the sense of `Logic.TangledHierarchies`.  Finiteness
  is the honest boundary: infinite serial frames such as `ω` with `n ↦ n+1` are
  loop-free, and that frame is exhibited (`omegaChain_serial_loopFree`) to show the
  hypothesis cannot be dropped.
* `iterSound_add`, `iterSound_zero` — the internal soundness degrees of a world form a
  submonoid of `(ℕ, +)`, the first step of conjecture C1.

## Relationship to catalog
Extends `Logic.ProvabilityLogic.SelfSoundSystems` (Cycle 4) and reuses `iterR`,
`transGen_of_iterR`, `sat_con_iff` from Cycle 3.
-/


open TangledSoundness

open GLPLogic

variable {α : Type}

/-! ## Part A — Degrees of internal soundness form a monoid -/




/-! ## Part B — Frame soundness and internal consistency -/





/-! ## Part C — Finite serial frames contain cycles -/





/-! ## Part D — The boundary: finiteness cannot be dropped -/





-- !-- Lab Notes -- !--
--
-- Hypothesis (Hypothesizer):
--   H16. Internal soundness degrees are closed under addition (conjecture C1, step 1).
--   H17. A system proving its own consistency admits only serial frame semantics, so
--        no nonempty converse well-founded frame can be sound for it.
--   H18. (Bold, the mission's claim) *Every finite* semantics of such a system is
--        tangled — a cycle is forced, not merely permitted.
--   H19. (Boundary) H18 fails without finiteness, witnessed by the ω-chain.
--
-- Experiment (Experimenter):
--   • H16: `iterR_add` (induction on the first length) transported through
--     `iterSound_iff_cycle`, giving `iterSound_add`.
--   • H17: `sat_con_iff` (Cycle 3) turns the theorem `¬□⊥` into seriality directly;
--     `WellFounded.has_min` then contradicts seriality on a nonempty frame.
--   • H18: `choose` extracts a successor function `f`; `Finite.exists_ne_map_eq_of_infinite`
--     applied to `n ↦ f^[n] w` gives a repeat `f^[i] w = f^[j] w`, and
--     `transGen_iterate` (induction with `Function.iterate_succ_apply'`) turns the gap
--     into a `TransGen` cycle.  Both orderings of `i, j` are handled.
--   • H19: `omegaChain`; transitive-closure edges strictly increase the index
--     (induction on `TransGen`), so no cycle exists.
--
-- Analysis (Analyst):
--   Survived: H16–H19, sorry-free.  The interesting failure is the *shape* of H18:
--   self-consistency alone forces only seriality, and seriality alone forces a cycle
--   only under finiteness — an infinite untangled model exists.  So the correct global
--   statement of "tangled hierarchies are unavoidable" is: unavoidable for finite
--   hierarchies, and unavoidable for well-founded ones in the strong sense that these
--   simply have no models at all (`isEmpty_of_provesCon_of_wf`).
--
-- Critique (Critic):
--   `provesCon_finite_isTangled` has genuinely satisfiable hypotheses:
--   `tangledSystem_frameSound_loopFrame` exhibits a system, a finite frame and the
--   consistency theorem together, so the result is not vacuously about an empty class.
--   The finiteness hypothesis is not a convenience: `omegaChain_serial_loopFree` shows
--   the conclusion fails without it, and this boundary is stated rather than hidden.
-- !-- Lab Notes -- !--
open TangledSoundness in
theorem solution{F : KFrame} {f : F.W → F.W} (hf : ∀ x, F.R x (f x))
    (w : F.W) : ∀ (i k : ℕ), 0 < k → Relation.TransGen F.R (f^[i] w) (f^[i + k] w) := by
  intro i k
  induction k with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simpa [Function.iterate_succ_apply'] using
          Relation.TransGen.single (hf (f^[i] w))
      · have hstep : Relation.TransGen F.R (f^[i + k] w) (f^[i + (k + 1)] w) := by
          have : f^[i + (k + 1)] w = f (f^[i + k] w) := by
            rw [show i + (k + 1) = (i + k) + 1 by ring, Function.iterate_succ_apply']
          rw [this]
          exact Relation.TransGen.single (hf (f^[i + k] w))
        exact (ih hk).trans hstep
