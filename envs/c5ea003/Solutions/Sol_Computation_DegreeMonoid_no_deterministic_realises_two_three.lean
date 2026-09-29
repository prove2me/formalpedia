-- Prove2me | solution 1 for Computation.DegreeMonoid.no_deterministic_realises_two_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:39:12.200246+00:00
-- url     : https://prove2.me/submissions/99e85ca5-e86e-4711-b206-5b13566ecb18

-- Sol generated from Speculative/AutoResearch/DegreeMonoidDeterminism.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidDeterminism
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
import Theorems.Thm_Computation_DegreeMonoid_closure_two_three
import Theorems.Thm_Computation_DegreeMonoid_deterministic_degreeMonoid_dvd
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
theorem solution{R : α → α → Prop} (hdet : Deterministic R) (a : α) :
    degreeMonoid R a ≠ AddSubmonoid.closure ({2, 3} : Set ℕ) := by
  intro hEq
  obtain ⟨d, _, hd⟩ := deterministic_degreeMonoid_dvd hdet a
  have h2 : (2 : ℕ) ∈ degreeMonoid R a := by
    rw [hEq]; exact AddSubmonoid.subset_closure (by simp)
  have h3 : (3 : ℕ) ∈ degreeMonoid R a := by
    rw [hEq]; exact AddSubmonoid.subset_closure (by simp)
  have hd2 : d ∣ 2 := (hd 2).1 h2
  have hd3 : d ∣ 3 := (hd 3).1 h3
  have hd1 : d = 1 := Nat.eq_one_of_dvd_coprimes (by decide) hd2 hd3
  have h1 : (1 : ℕ) ∈ degreeMonoid R a := (hd 1).2 (by rw [hd1])
  rw [hEq] at h1
  have : (1 : ℕ) ∈ {k : ℕ | k = 0 ∨ 2 ≤ k} := by
    rw [← closure_two_three]; exact h1
  simp only [Set.mem_setOf_eq] at this
  omega
