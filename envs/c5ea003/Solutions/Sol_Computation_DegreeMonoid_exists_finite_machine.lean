-- Prove2me | solution 1 for Computation.DegreeMonoid.exists_finite_machine
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:38:07.697906+00:00
-- url     : https://prove2.me/submissions/4ffd2047-bedc-4c20-bd23-f46d12feee9e

-- Sol generated from Speculative/AutoResearch/DegreeMonoidDeterminism.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidDeterminism
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
import Theorems.Thm_Computation_DegreeMonoid_degreeMonoid_chainRel
import Theorems.Thm_Computation_DegreeMonoid_degreeMonoid_eq_of_bisim
/-
# Determinism, gaps, and finite-state realisation of degree monoids

Two further layers on top of `Computation.DegreeMonoidRealisation` and
`Computation.DegreeMonoidStructure`.

**Determinism.**  For a *deterministic* transition relation the degree monoid of a state is
closed under subtraction, hence is the full arithmetic progression `dℕ`
(`deterministic_degreeMonoid_dvd`): a deterministic machine has **no gaps**
(`deterministic_no_gaps`).  Consequently the existence of a single gap is a certificate of
nondeterminism (`nondeterministic_of_gap`), and *no* deterministic machine — on any state
space whatsoever — can have the numerical semigroup `⟨2,3⟩` as its degree monoid
(`no_deterministic_realises_two_three`).  The invariant therefore separates deterministic
from nondeterministic computation.

**Finite state spaces.**  Using that every additive submonoid of `ℕ` is finitely generated,
the realisation theorem can be upgraded: every submonoid of `ℕ` is the degree monoid of a
state of a machine with *finitely many* states (`exists_finite_machine`), so finite
nondeterministic machines already realise the whole invariant lattice
(`finite_state_degreeMonoid_range`).

All results are proved with no `sorry`.
-/

open Computation
open DegreeMonoid

variable {α : Type*}

/-! ## Deterministic systems -/









/-! ## Determinism on a finite state space bounds the period -/


/-! ## Finite-state realisation -/




open Computation.DegreeMonoid in
theorem solution(M : AddSubmonoid ℕ) :
    ∃ (B : ℕ) (R : Fin (B + 1) → Fin (B + 1) → Prop) (a : Fin (B + 1)),
      degreeMonoid R a = M := by
  classical
  obtain ⟨t, ht⟩ := Nat.addSubmonoid_fg M
  set B := t.sup id with hB
  have hbound : ∀ s ∈ (t : Set ℕ), s ≤ B := by
    intro s hs
    exact Finset.le_sup (f := id) (by simpa using hs)
  refine ⟨B, fun x y => chainRel (t : Set ℕ) x.val y.val, ⟨0, Nat.succ_pos B⟩, ?_⟩
  have hbisim :
      degreeMonoid (fun x y : Fin (B + 1) => chainRel (t : Set ℕ) x.val y.val)
          ⟨0, Nat.succ_pos B⟩
        = degreeMonoid (chainRel (t : Set ℕ)) 0 := by
    have := degreeMonoid_eq_of_bisim (R := fun x y : Fin (B + 1) => chainRel (t : Set ℕ) x.val y.val)
      (S := chainRel (t : Set ℕ)) (f := Fin.val) Fin.val_injective
      (fun _ _ => Iff.rfl)
      (fun x y hxy => by
        rcases hxy with ⟨_, hmem⟩ | hstep
        · exact ⟨⟨y, by have := hbound (y + 1) hmem; omega⟩, rfl⟩
        · exact ⟨⟨y, by omega⟩, rfl⟩)
      ⟨0, Nat.succ_pos B⟩
    simpa using this
  rw [hbisim, degreeMonoid_chainRel, ht]
