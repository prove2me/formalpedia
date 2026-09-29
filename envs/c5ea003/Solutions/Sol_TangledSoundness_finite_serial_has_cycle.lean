-- Prove2me | solution 1 for TangledSoundness.finite_serial_has_cycle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:46:32.216982+00:00
-- url     : https://prove2.me/submissions/2e27524d-654f-402c-a6f6-891eba4389b0

-- Sol generated from Logic/ProvabilityLogic/SelfConsistentSemantics.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_SelfConsistentSemantics
import Definitions.Def_Logic_ProvabilityLogic_SelfSoundSystems
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
import Theorems.Thm_TangledSoundness_transGen_iterate
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
theorem solution(F : KFrame) [Finite F.W] [Nonempty F.W]
    (hser : ∀ w : F.W, ∃ v, F.R w v) : ∃ w : F.W, Relation.TransGen F.R w w := by
  classical
  choose f hf using hser
  obtain ⟨w⟩ := ‹Nonempty F.W›
  obtain ⟨i, j, hij, hfe⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] w)
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨f^[i] w, ?_⟩
    have hk : 0 < j - i := by omega
    have := transGen_iterate hf w i (j - i) hk
    rwa [show i + (j - i) = j by omega, ← hfe] at this
  · have hlt : j < i := by omega
    refine ⟨f^[j] w, ?_⟩
    have hk : 0 < i - j := by omega
    have := transGen_iterate hf w j (i - j) hk
    rwa [show j + (i - j) = i by omega, hfe] at this
