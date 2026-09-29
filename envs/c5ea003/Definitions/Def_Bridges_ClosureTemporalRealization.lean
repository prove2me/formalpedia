-- Prove2me | Definitions.Def_Bridges_ClosureTemporalRealization
-- name    : Bridges_ClosureTemporalRealization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:58.165082+00:00
-- url     : https://prove2.me/theorems/f5684f84-32e3-4d91-acb8-15d104fdfabb
-- title:
--   Aether Catalog definitions — Bridges_ClosureTemporalRealization
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureTemporalRealization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureTemporalRealization.lean by skeleton subtraction
import Mathlib

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

namespace ClosureTemporalRealization

universe u v w

variable {M : Type u} {Time : Type v}

/-! ## §1. Closure Operators -/


/-! ## §2. Reversible Delay Actions -/


/-! ## §3. Observational Equivalence -/

/-- Observational equivalence: two elements have identical temporal response profiles. -/
def obsEquiv (H : M → Time → M → Prop) (x y : M) : Prop :=
  ∀ t z, H x t z ↔ H y t z


theorem obsEquiv_symm' (H : M → Time → M → Prop) {x y : M}
    (h : obsEquiv H x y) : obsEquiv H y x :=
  fun t z => (h t z).symm

theorem obsEquiv_trans' (H : M → Time → M → Prop) {x y z : M}
    (h₁ : obsEquiv H x y) (h₂ : obsEquiv H y z) : obsEquiv H x z :=
  fun t w => (h₁ t w).trans (h₂ t w)



/-! ## §4. Finite Reversible Schedulers -/

/-- A finite reversible scheduler. -/
structure FinRevScheduler (Time : Type v) (Event : Type u) where
  State : Type u
  step : State → Time → State
  emit : State → Event → Prop
  revState : State → State
  instFintype : Fintype State
  rev_invol : Involutive revState
  step_rev : ∀ q t, revState (step q t) = step (revState q) t

attribute [instance] FinRevScheduler.instFintype

/-- A realization witnesses that a scheduler implements a response function. -/
structure SchedulerRealization (H : M → Time → M → Prop)
    (S : FinRevScheduler Time M) where
  enc : M → S.State
  correct : ∀ x t y, H x t y ↔ S.emit (S.step (enc x) t) y

/-! ## §5. Finite Response Rank -/

/-- The response function has **finite rank**: it factors through a finite set
    of temporal profiles. -/
def FiniteResponseRank (H : M → Time → M → Prop) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (φ : M → ι),
    ∀ x y, φ x = φ y → obsEquiv H x y

/-! ## §6. Forward Direction: Realization ⟹ Finite Rank -/


/-! ## §7. Temporal Response Systems -/

/-- A temporal response system packages a response function with delay and
    reversal structure satisfying compatibility axioms. -/
structure TemporalResponseSystem (M : Type u) (Time : Type v) where
  H : M → Time → M → Prop
  delay : Time → M → M
  rev : M → M
  zero : Time
  time_shift : ∀ x t y, H x t y ↔ H (delay t x) zero y
  delay_compat : ∀ t x y, obsEquiv H x y → obsEquiv H (delay t x) (delay t y)
  rev_involutive : Involutive rev
  rev_compat : ∀ x y, obsEquiv H x y → obsEquiv H (rev x) (rev y)
  delay_rev_comm : ∀ t x, rev (delay t x) = delay t (rev x)

/-! ## §8. Exact Finite Factorization -/

/-- An exact finite factorization of a response function. -/
structure ExactFiniteRank (H : M → Time → M → Prop) where
  ι : Type u
  instFintype : Fintype ι
  φ : M → ι
  φ_surj : Surjective φ
  sound : ∀ x y, φ x = φ y → obsEquiv H x y
  complete : ∀ x y, obsEquiv H x y → φ x = φ y

attribute [instance] ExactFiniteRank.instFintype


/-! ## §9. Canonical Scheduler Construction -/

section CanonicalConstruction

variable (T : TemporalResponseSystem M Time) (E : ExactFiniteRank T.H)

private def repr' : E.ι → M := fun i => (E.φ_surj i).choose

private theorem repr'_spec (i : E.ι) : E.φ (repr' T E i) = i :=
  (E.φ_surj i).choose_spec

private theorem repr'_obsEquiv_of_eq (x : M) :
    obsEquiv T.H (repr' T E (E.φ x)) x := by
  apply E.sound
  exact repr'_spec T E (E.φ x)

private def canonStep : E.ι → Time → E.ι :=
  fun i t => E.φ (T.delay t (repr' T E i))

private def canonEmit : E.ι → M → Prop :=
  fun i y => T.H (repr' T E i) T.zero y

private def canonRev : E.ι → E.ι :=
  fun i => E.φ (T.rev (repr' T E i))

private theorem canonRev_involutive : Involutive (canonRev T E) := by
  intro i
  simp only [canonRev]
  -- Let j = φ(rev(repr' i)). Need: φ(rev(repr' j)) = i.
  set j := E.φ (T.rev (repr' T E i))
  -- repr' j ~ rev(repr' i) since φ(repr' j) = j = φ(rev(repr' i))
  have key : E.φ (repr' T E j) = E.φ (T.rev (repr' T E i)) := repr'_spec T E j
  have h1 := E.sound _ _ key
  -- rev(repr' j) ~ rev(rev(repr' i)) = repr' i
  have h2 := T.rev_compat _ _ h1
  rw [T.rev_involutive] at h2
  -- φ(rev(repr' j)) = φ(repr' i) = i
  have h3 := E.complete _ _ h2
  rw [repr'_spec T E i] at h3
  exact h3

private theorem canonStep_rev :
    ∀ q t, canonRev T E (canonStep T E q t) = canonStep T E (canonRev T E q) t := by
  intro q t
  simp only [canonRev, canonStep]
  have h1 := repr'_obsEquiv_of_eq T E (T.delay t (repr' T E q))
  have h2 := T.rev_compat _ _ h1
  rw [T.delay_rev_comm] at h2
  have h3 := repr'_obsEquiv_of_eq T E (T.rev (repr' T E q))
  have h4 := T.delay_compat t _ _ h3
  exact E.complete _ _ (obsEquiv_trans' T.H h2 (obsEquiv_symm' T.H h4))

/-- The canonical finite reversible scheduler. -/
def canonicalScheduler : FinRevScheduler Time M where
  State := E.ι
  step := canonStep T E
  emit := canonEmit T E
  revState := canonRev T E
  instFintype := E.instFintype
  rev_invol := canonRev_involutive T E
  step_rev := canonStep_rev T E

def canonEnc : M → E.ι := E.φ

/-- The canonical scheduler correctly realizes the response function. -/
theorem canonical_correct :
    ∀ x t y, T.H x t y ↔ canonEmit T E (canonStep T E (canonEnc T E x) t) y := by
  intro x t y
  simp only [canonEmit, canonStep, canonEnc]
  rw [T.time_shift]
  have hrepr : obsEquiv T.H x (repr' T E (E.φ x)) :=
    obsEquiv_symm' T.H (repr'_obsEquiv_of_eq T E x)
  have hdelay : obsEquiv T.H (T.delay t x) (T.delay t (repr' T E (E.φ x))) :=
    T.delay_compat t _ _ hrepr
  have hrepr2 : obsEquiv T.H (repr' T E (E.φ (T.delay t (repr' T E (E.φ x)))))
      (T.delay t (repr' T E (E.φ x))) :=
    repr'_obsEquiv_of_eq T E _
  have h1 : obsEquiv T.H (repr' T E (E.φ (T.delay t (repr' T E (E.φ x)))))
      (T.delay t x) :=
    obsEquiv_trans' T.H hrepr2 (obsEquiv_symm' T.H hdelay)
  exact (h1 T.zero y).symm

/-- The canonical scheduler realization. -/
def canonical_realizes : SchedulerRealization T.H (canonicalScheduler T E) where
  enc := canonEnc T E
  correct := canonical_correct T E

end CanonicalConstruction

/-! ## §10. Main Duality Theorem -/



/-! ## §11. Stable Temporal Principal Basis -/

/-- A stable temporal principal basis: a finite set of representatives whose
    observational classes cover all of `M`. -/
def StableTemporalPrincipalBasis (H : M → Time → M → Prop) : Prop :=
  ∃ (B : Finset M), ∀ x, ∃ b ∈ B, obsEquiv H x b

/-
Exact finite rank implies a stable temporal principal basis.
-/

/-
A stable temporal principal basis implies finite response rank.
-/


/-! ## §12. Minimality -/

/-- A realization is **minimal** if encoding captures observational equivalence exactly. -/
def IsMinimalRealization (H : M → Time → M → Prop)
    (S : FinRevScheduler Time M) (r : SchedulerRealization H S) : Prop :=
  ∀ x y, r.enc x = r.enc y ↔ obsEquiv H x y



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

end ClosureTemporalRealization

end


