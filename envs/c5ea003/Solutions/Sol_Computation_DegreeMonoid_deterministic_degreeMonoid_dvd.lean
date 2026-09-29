-- Prove2me | solution 1 for Computation.DegreeMonoid.deterministic_degreeMonoid_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:36:45.854145+00:00
-- url     : https://prove2.me/submissions/daf5e753-f76c-4863-bb74-3ea1509e2593

-- Sol generated from Speculative/AutoResearch/DegreeMonoidDeterminism.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidDeterminism
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
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


/-- In a deterministic system a path of given length has a unique endpoint. -/
theorem iterR_unique {R : α → α → Prop} (hdet : Deterministic R) :
    ∀ (n : ℕ) (a b c : α), iterR R n a b → iterR R n a c → b = c := by
  intro n
  induction n with
  | zero => intro a b c hb hc; exact hb ▸ hc
  | succ n ih =>
      rintro a b c ⟨x, hx, hxb⟩ ⟨y, hy, hyc⟩
      have : x = y := hdet a x y hx hy
      subst this
      exact ih x b c hxb hyc

/-- **Subtraction closure.**  The degree monoid of a state of a deterministic system is
closed under (truncated) subtraction. -/
theorem deterministic_sub_mem {R : α → α → Prop} (hdet : Deterministic R) {a : α} {m n : ℕ}
    (hm : m ∈ degreeMonoid R a) (hn : n ∈ degreeMonoid R a) (hmn : m ≤ n) :
    n - m ∈ degreeMonoid R a := by
  have hsplit : n = m + (n - m) := by omega
  rw [hsplit] at hn
  obtain ⟨b, hb1, hb2⟩ := (iterR_add R m (n - m) a a).1 hn
  have : b = a := iterR_unique hdet m a b a hb1 hm
  exact this ▸ hb2






/-! ## Determinism on a finite state space bounds the period -/


/-! ## Finite-state realisation -/




open Computation.DegreeMonoid in
theorem solution{R : α → α → Prop} (hdet : Deterministic R) (a : α) :
    ∃ d : ℕ, d ∈ degreeMonoid R a ∧ ∀ n : ℕ, n ∈ degreeMonoid R a ↔ d ∣ n := by
  by_cases hex : ∃ k : ℕ, (k + 1) ∈ degreeMonoid R a
  · classical
    set d := Nat.find hex + 1 with hd
    have hdmem : d ∈ degreeMonoid R a := Nat.find_spec hex
    have hmin : ∀ m ∈ degreeMonoid R a, m ≠ 0 → d ≤ m := by
      intro m hm hm0
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have : Nat.find hex ≤ j := Nat.find_le hm
      omega
    have hmul : ∀ c : ℕ, d * c ∈ degreeMonoid R a := by
      intro c
      induction c with
      | zero => simp
      | succ c ih =>
          have : d * (c + 1) = d * c + d := by ring
          rw [this]
          exact add_mem ih hdmem
    refine ⟨d, hdmem, fun n => ⟨fun hn => ?_, fun ⟨c, hc⟩ => hc ▸ hmul c⟩⟩
    have hdpos : 0 < d := by omega
    have hq : d * (n / d) ∈ degreeMonoid R a := hmul (n / d)
    have hle : d * (n / d) ≤ n := by
      have := Nat.div_add_mod n d
      omega
    have hrem : n - d * (n / d) ∈ degreeMonoid R a := deterministic_sub_mem hdet hq hn hle
    have hmod : n - d * (n / d) = n % d := by
      have := Nat.div_add_mod n d
      omega
    rw [hmod] at hrem
    by_contra hdvd
    have hne : n % d ≠ 0 := fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    have := hmin _ hrem hne
    have := Nat.mod_lt n hdpos
    omega
  · -- no nonzero closed computation: the degree monoid is `{0}`
    push_neg at hex
    refine ⟨0, zero_mem _, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
    · cases n with
      | zero => exact dvd_rfl
      | succ j => exact absurd hn (hex j)
    · have : n = 0 := Nat.eq_zero_of_zero_dvd hn
      exact this ▸ zero_mem _
