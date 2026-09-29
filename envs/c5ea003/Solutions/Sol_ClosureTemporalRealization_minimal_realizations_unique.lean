-- Prove2me | solution 1 for ClosureTemporalRealization.minimal_realizations_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:10:50.10193+00:00
-- url     : https://prove2.me/submissions/3335cfd3-c0d8-43cc-aa1f-d02ee206df79

-- Sol generated from Bridges/ClosureTemporalRealization.lean
import Mathlib
import Definitions.Def_Bridges_ClosureTemporalRealization

/-!
# Closure-Delay Temporal Realization Duality

This file establishes a realization duality theorem at the interface of closure
operators, delay actions, reversible computation, and finite reconstruction.

The main result is a **temporal Myhill–Nerode theorem**: the observational
equivalence classes of a temporal response function determine a canonical
minimal reversible scheduler, which is unique up to isomorphism.

## Main Results

* `obsEquiv_equivalence` — Temporal observational equivalence is an equivalence relation.
* `realization_implies_finite_rank` — Any finite reversible scheduler realization
  implies finite response rank.
* `canonical_realizes` — The canonical quotient scheduler realizes the response.
* `closure_delay_realization_duality` — Realizability ↔ finite response rank.
* `finite_rank_iff_stable_basis` — Finite rank ↔ stable temporal principal basis.
* `canonical_is_minimal` — The canonical scheduler is minimal.
* `minimal_realizations_unique` — Uniqueness of minimal realizations up to bijection.
* `reconstruct_minimal_scheduler` — Certified reconstruction with minimality and uniqueness.
* `synchronous_product_finite_rank` — Compositionality under synchronous product.
-/

noncomputable section

open Function Set

open ClosureTemporalRealization

universe u v w

variable {M : Type u} {Time : Type v}

/-! ## §1. Closure Operators -/


/-! ## §2. Reversible Delay Actions -/


/-! ## §3. Observational Equivalence -/







/-! ## §4. Finite Reversible Schedulers -/


attribute [instance] FinRevScheduler.instFintype


/-! ## §5. Finite Response Rank -/


/-! ## §6. Forward Direction: Realization ⟹ Finite Rank -/


/-! ## §7. Temporal Response Systems -/


/-! ## §8. Exact Finite Factorization -/


attribute [instance] ExactFiniteRank.instFintype


/-! ## §9. Canonical Scheduler Construction -/


variable (T : TemporalResponseSystem M Time) (E : ExactFiniteRank T.H)














/-! ## §10. Main Duality Theorem -/



/-! ## §11. Stable Temporal Principal Basis -/


/-
Exact finite rank implies a stable temporal principal basis.
-/

/-
A stable temporal principal basis implies finite response rank.
-/


/-! ## §12. Minimality -/




/-! ## §13. Uniqueness of Minimal Realizations -/

/-
Given two minimal realizations with surjective encodings, there is a
    bijection between their state spaces intertwining the encodings.
-/

/-! ## §14. Certified Reconstruction -/

/-
Full certified reconstruction: from exact finite rank, produce a minimal
    realization unique up to bijective state relabeling.
-/

/-! ## §15. Compositionality: Synchronous Product -/

variable {M₁ M₂ : Type u}

/-
Observational equivalence for product response decomposes componentwise
    when the response is a conjunction.
-/

/-
If both components have finite rank, the product response has finite rank.
-/



open ClosureTemporalRealization in
theorem solution    (H : M → Time → M → Prop)
    (S₁ : FinRevScheduler Time M) (r₁ : SchedulerRealization H S₁)
    (hmin₁ : IsMinimalRealization H S₁ r₁)
    (S₂ : FinRevScheduler Time M) (r₂ : SchedulerRealization H S₂)
    (hmin₂ : IsMinimalRealization H S₂ r₂)
    (h₁_surj : Surjective r₁.enc) (h₂_surj : Surjective r₂.enc) :
    ∃ f : S₁.State → S₂.State, Bijective f ∧
      ∀ x, f (r₁.enc x) = r₂.enc x := by
  -- Define the function $f : S₁.State → S₂.State$ as follows: given $q₁ : S₁.State$, by $h₁_surj$ there exists $x$ with $r₁.enc x = q₁$. Define $f q₁ = r₂.enc x$.
  obtain ⟨f, hf⟩ : ∃ f : S₁.State → S₂.State, ∀ x, f (r₁.enc x) = r₂.enc x := by
    use fun q => r₂.enc (Classical.choose (h₁_surj q));
    intro x;
    have := Classical.choose_spec ( h₁_surj ( r₁.enc x ) );
    exact hmin₂ _ _ |>.2 ( hmin₁ _ _ |>.1 this );
  refine' ⟨ f, ⟨ _, _ ⟩, hf ⟩;
  · intro x y hxy;
    obtain ⟨ x', rfl ⟩ := h₁_surj x; obtain ⟨ y', rfl ⟩ := h₁_surj y
    have h1 := (hf x').symm.trans hxy |>.trans (hf y')
    exact (hmin₁ x' y').mpr ((hmin₂ x' y').mp h1)
  · exact fun x => by obtain ⟨ y, rfl ⟩ := h₂_surj x; exact ⟨ _, hf y ⟩ ;
