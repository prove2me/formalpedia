-- Prove2me | solution 2 for Round10.least_complete_exponent_prod
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:18:51.007407+00:00
-- url     : https://prove2.me/submissions/d86a3e74-ff75-4fb5-b6d0-decbfbe69d25

import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
open Round10 Finset in
theorem solution (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime) :
    IsLeast {m : ℕ | 0 < m ∧ freeWitness (∏ r ∈ P, r) m = ∏ r ∈ P, (r - 1)}
      (P.lcm (fun r => r - 1)) := by
  -- the full count is reached exactly at the common multiples of the `r - 1`
  have hiff : ∀ k : ℕ, freeWitness (∏ r ∈ P, r) k = ∏ r ∈ P, (r - 1) ↔ ∀ r ∈ P, (r - 1) ∣ k := by
    intro k
    -- `φ` of a product of distinct primes
    have htot : ∀ Q : Finset ℕ, (∀ r ∈ Q, r.Prime) → Nat.totient (∏ r ∈ Q, r) = ∏ r ∈ Q, (r - 1) := by
      intro Q
      induction Q using Finset.induction_on with
      | empty => intro _; simp
      | @insert a s ha ih =>
        intro hQ
        have hpa := hQ a (mem_insert_self a s)
        have hcop : Nat.Coprime a (∏ r ∈ s, r) := Nat.Coprime.prod_right (fun r hr =>
          (Nat.coprime_primes hpa (hQ r (mem_insert_of_mem hr))).2 (fun h => ha (h ▸ hr)))
        rw [prod_insert ha, prod_insert ha, Nat.totient_mul hcop, Nat.totient_prime hpa,
          ih (fun r hr => hQ r (mem_insert_of_mem hr))]
    have hN0 : (∏ r ∈ P, r) ≠ 0 := prod_ne_zero_iff.2 (fun r hr => (hP r hr).ne_zero)
    haveI : NeZero (∏ r ∈ P, r) := ⟨hN0⟩
    have hdvd : ∀ r ∈ P, r ∣ ∏ r ∈ P, r := fun r hr => dvd_prod_of_mem _ hr
    have hcard : Nat.card (ZMod (∏ r ∈ P, r))ˣ = ∏ r ∈ P, (r - 1) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, htot P hP]
    -- the count is the whole unit group iff every unit is a `k`-th root of unity
    have hall : freeWitness (∏ r ∈ P, r) k = ∏ r ∈ P, (r - 1)
        ↔ ∀ x : (ZMod (∏ r ∈ P, r))ˣ, x ^ k = 1 := by
      rw [← hcard, freeWitness, rootCount]
      constructor
      · intro h x
        by_contra hx
        have : Nat.card {y : (ZMod (∏ r ∈ P, r))ˣ // y ^ k = 1} < Nat.card (ZMod (∏ r ∈ P, r))ˣ :=
          Finite.card_subtype_lt hx
        omega
      · intro h
        exact Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [hall]
    constructor
    · intro h r hr
      haveI := Fact.mk (hP r hr)
      have hall_r : ∀ y : (ZMod r)ˣ, y ^ k = 1 := by
        intro y
        obtain ⟨x, rfl⟩ := ZMod.unitsMap_surjective (hdvd r hr) y
        rw [← map_pow, h x, map_one]
      have := Monoid.exponent_dvd_of_forall_pow_eq_one hall_r
      rwa [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units r] at this
    · intro h x
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have key : ∀ r ∈ P, r ∣ ((x : ZMod (∏ r ∈ P, r)) ^ k - 1).val := by
        intro r hr
        haveI := Fact.mk (hP r hr)
        have hu : (ZMod.unitsMap (hdvd r hr) x) ^ k = 1 := by
          obtain ⟨m, hm⟩ := h r hr
          rw [hm, pow_mul, ZMod.units_pow_card_sub_one_eq_one, one_pow]
        have hv := congrArg Units.val hu
        rw [Units.val_pow_eq_pow_val, Units.val_one, ZMod.unitsMap_val] at hv
        have hc : ZMod.castHom (hdvd r hr) (ZMod r) ((x : ZMod (∏ r ∈ P, r)) ^ k - 1) = 0 := by
          rw [map_sub, map_pow, map_one, ZMod.castHom_apply, hv, sub_self]
        rw [← ZMod.natCast_zmod_val ((x : ZMod (∏ r ∈ P, r)) ^ k - 1), map_natCast] at hc
        exact (ZMod.natCast_eq_zero_iff _ _).mp hc
      have hprod := prod_primes_dvd _ (fun r hr => (hP r hr).prime) key
      rw [← sub_eq_zero, ← ZMod.natCast_zmod_val ((x : ZMod (∏ r ∈ P, r)) ^ k - 1)]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hprod
  have hl0 : 0 < P.lcm (fun r => r - 1) := by
    refine Nat.pos_of_ne_zero (fun h => ?_)
    obtain ⟨r, hr, h0⟩ := Finset.lcm_eq_zero_iff.1 h
    have := (hP r hr).two_le
    omega
  refine ⟨⟨hl0, (hiff _).2 (fun r hr => Finset.dvd_lcm hr)⟩, ?_⟩
  rintro m ⟨hm0, hm⟩
  exact Nat.le_of_dvd hm0 (Finset.lcm_dvd ((hiff m).1 hm))
