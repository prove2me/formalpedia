-- Prove2me | solution 1 for Computation.DegreeMonoid.deterministic_degPeriod_le_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:38:00.713435+00:00
-- url     : https://prove2.me/submissions/28e248b4-68b2-47ad-9a14-8cb81aff6cde

-- Sol generated from Speculative/AutoResearch/DegreeMonoidDeterminism.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidDeterminism
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
import Theorems.Thm_Computation_DegreeMonoid_degPeriod_dvd_mem
import Theorems.Thm_Computation_DegreeMonoid_degPeriod_pos
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





/-- For deterministic machines the period generates the whole degree monoid. -/
theorem deterministic_degPeriod_spec {R : α → α → Prop} (hdet : Deterministic R) (a : α) :
    ∀ n : ℕ, n ∈ degreeMonoid R a ↔ degPeriod R a ∣ n := by
  obtain ⟨d, hdmem, hd⟩ := deterministic_degreeMonoid_dvd hdet a
  have h1 : degPeriod R a ∣ d := degPeriod_dvd_mem hdmem
  have h2 : d ∣ degPeriod R a := by
    rw [degPeriod, Nat.dvd_setGcd_iff]
    intro m hm
    exact (hd m).1 (by exact hm)
  have : degPeriod R a = d := Nat.dvd_antisymm h1 h2
  rw [this]
  exact hd




/-! ## Determinism on a finite state space bounds the period -/


/-! ## Finite-state realisation -/




open Computation.DegreeMonoid in
theorem solution[Fintype α] {R : α → α → Prop}
    (hdet : Deterministic R) (a : α) (hlive : ∃ n ∈ degreeMonoid R a, n ≠ 0) :
    degPeriod R a ≤ Fintype.card α := by
  classical
  obtain ⟨n0, hn0, hn0'⟩ := hlive
  set d := degPeriod R a with hdd
  have hdpos : 0 < d := degPeriod_pos hn0 hn0'
  have hd : ∀ n : ℕ, n ∈ degreeMonoid R a ↔ d ∣ n := deterministic_degPeriod_spec hdet a
  have hdmem : iterR R d a a := (hd d).2 dvd_rfl
  have hex : ∀ i, i < d → ∃ s, iterR R i a s ∧ iterR R (d - i) s a := by
    intro i hi
    have hsplit : d = i + (d - i) := by omega
    rw [hsplit] at hdmem
    exact (iterR_add R i (d - i) a a).1 hdmem
  have key : ∀ i j : Fin d, i.val < j.val →
      Classical.choose (hex i.1 i.2) ≠ Classical.choose (hex j.1 j.2) := by
    intro i j hij heq
    obtain ⟨hi1, -⟩ := Classical.choose_spec (hex i.1 i.2)
    obtain ⟨-, hj2⟩ := Classical.choose_spec (hex j.1 j.2)
    have hloop : iterR R (i.1 + (d - j.1)) a a :=
      (iterR_add R i.1 (d - j.1) a a).2 ⟨_, hi1, heq ▸ hj2⟩
    have hdvd : d ∣ (i.1 + (d - j.1)) := (hd _).1 hloop
    have h1 : 0 < i.1 + (d - j.1) := by omega
    have h2 : i.1 + (d - j.1) < d := by omega
    have := Nat.le_of_dvd h1 hdvd
    omega
  have hinj : Function.Injective (fun i : Fin d => Classical.choose (hex i.1 i.2)) := by
    intro i j hij
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact absurd hij (key i j h)
    · exact Fin.ext h
    · exact absurd hij.symm (key j i h)
  have := Fintype.card_le_of_injective _ hinj
  simpa using this
