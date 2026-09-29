-- Prove2me | solution 1 for Computation.DegreeMonoid.degPeriod_prodRel
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:36:44.420717+00:00
-- url     : https://prove2.me/submissions/bf8ab7c9-4337-439e-81da-88cca09561d8

-- Sol generated from Speculative/AutoResearch/DegreeMonoidStructure.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
import Theorems.Thm_Computation_DegreeMonoid_degPeriod_dvd_mem
import Theorems.Thm_Computation_DegreeMonoid_degPeriod_pos
import Theorems.Thm_Computation_DegreeMonoid_degreeMonoid_prodRel
import Theorems.Thm_Computation_DegreeMonoid_mem_degreeMonoid
/-
# Structure theory of degree monoids: period, gaps and the Frobenius obstruction

`Computation.DegreeMonoidRealisation` shows that the degree monoid
`degreeMonoid R a ≤ ℕ` of a state of a transition system is a complete invariant for the
lattice of additive submonoids of `ℕ`: *every* submonoid is realised by the chain machine
`chainRel M`.  Completeness of a realisation problem is only half the story — the other
half is the *structure* of the realised objects.  This file supplies it:

* `degPeriod R a` — the period of a state, the gcd of all its closed-computation lengths;
* `degPeriod_dvd_mem` and `exists_ge_mem_degreeMonoid` — the **structure theorem**: every
  closed computation has length divisible by the period, and conversely *every*
  sufficiently large multiple of the period is a closed-computation length.  So the degree
  monoid is an eventually complete arithmetic progression;
* `degreeMonoid_gaps_finite` — a state has only finitely many *gaps* (multiples of the
  period which are not computation lengths);
* `degPeriod_eq_zero_iff` — the sharp dichotomy: period `0` exactly for the dead state
  (`degreeMonoid = ⊥`);
* `degPeriod_prodRel` — the **synchronisation law**: the period of a synchronous product of
  two live machines is the *least common multiple* of the two periods;
* `frobenius_gap_of_chainRel` — a number-theoretic bridge: for coprime `p, q > 1` the chain
  machine of `⟨p, q⟩` has largest gap exactly `p*q - p - q` (Chicken McNugget/Frobenius),
  and `frobenius_gap_two_three` specialises this to the certified sample value `⟨2,3⟩`,
  whose unique gap is the length `1`.

All results are proved with no `sorry`.
-/

open Computation
open DegreeMonoid

variable {α β : Type*}

/-! ## The period of a state -/



/-- **Structure theorem.**  All sufficiently large multiples of the period are lengths of
closed computations. -/
theorem exists_ge_mem_degreeMonoid (R : α → α → Prop) (a : α) :
    ∃ N : ℕ, ∀ m ≥ N, degPeriod R a ∣ m → m ∈ degreeMonoid R a := by
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (degreeMonoid R a : Set ℕ)
  refine ⟨N, fun m hm hdvd => ?_⟩
  have := hN m hm hdvd
  rwa [AddSubmonoid.closure_eq] at this





/-! ## Synchronisation: periods multiply to their lcm under products -/



/-! ## The Frobenius obstruction of a two-loop machine -/





open Computation.DegreeMonoid in
theorem solution{R : α → α → Prop} {S : β → β → Prop} {a : α} {b : β}
    (ha : ∃ n ∈ degreeMonoid R a, n ≠ 0) (hb : ∃ n ∈ degreeMonoid S b, n ≠ 0) :
    degPeriod (prodRel R S) (a, b) = Nat.lcm (degPeriod R a) (degPeriod S b) := by
  obtain ⟨n1, hn1, hn1'⟩ := ha
  obtain ⟨n2, hn2, hn2'⟩ := hb
  have hp1 : 0 < degPeriod R a := degPeriod_pos hn1 hn1'
  have hp2 : 0 < degPeriod S b := degPeriod_pos hn2 hn2'
  set d1 := degPeriod R a
  set d2 := degPeriod S b
  set L := Nat.lcm d1 d2 with hL
  have hLpos : 0 < L := Nat.pos_of_ne_zero (by
    simp only [hL, Ne, Nat.lcm_eq_zero_iff]
    omega)
  have hmem : ∀ n : ℕ, n ∈ degreeMonoid (prodRel R S) (a, b) ↔
      n ∈ degreeMonoid R a ∧ n ∈ degreeMonoid S b := by
    intro n
    rw [degreeMonoid_prodRel]
    simp
  -- The lcm divides every element of the product's degree monoid.
  have hdvd1 : L ∣ degPeriod (prodRel R S) (a, b) := by
    rw [degPeriod, Nat.dvd_setGcd_iff]
    intro m hm
    have hm' := (hmem m).1 (by exact hm)
    exact Nat.lcm_dvd (degPeriod_dvd_mem hm'.1) (degPeriod_dvd_mem hm'.2)
  -- Conversely, two consecutive large multiples of the lcm are both realised.
  obtain ⟨N1, hN1⟩ := exists_ge_mem_degreeMonoid R a
  obtain ⟨N2, hN2⟩ := exists_ge_mem_degreeMonoid S b
  set K := max N1 N2 + 1 with hK
  have hbig : ∀ k : ℕ, K ≤ k → L * k ∈ degreeMonoid (prodRel R S) (a, b) := by
    intro k hk
    have hge : max N1 N2 ≤ L * k := by
      calc max N1 N2 ≤ k := by omega
        _ ≤ L * k := Nat.le_mul_of_pos_left k hLpos
    refine (hmem (L * k)).2 ⟨hN1 _ (le_trans (le_max_left _ _) hge) ?_,
      hN2 _ (le_trans (le_max_right _ _) hge) ?_⟩
    · exact Dvd.dvd.mul_right (Nat.dvd_lcm_left d1 d2) k
    · exact Dvd.dvd.mul_right (Nat.dvd_lcm_right d1 d2) k
  have h1 : degPeriod (prodRel R S) (a, b) ∣ L * K := degPeriod_dvd_mem (hbig K le_rfl)
  have h2 : degPeriod (prodRel R S) (a, b) ∣ L * (K + 1) :=
    degPeriod_dvd_mem (hbig (K + 1) (by omega))
  have hdvd2 : degPeriod (prodRel R S) (a, b) ∣ L := by
    have := Nat.dvd_sub h2 h1
    simpa [Nat.mul_succ] using this
  exact Nat.dvd_antisymm hdvd2 hdvd1
