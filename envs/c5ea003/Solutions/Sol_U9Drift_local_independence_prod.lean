-- Prove2me | solution 1 for U9Drift.local_independence_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:48:59.776088+00:00
-- url     : https://prove2.me/submissions/02bbf68f-b5fe-4dfd-ac2c-30353af60902

-- Sol generated from Probability/U9DriftLocalIndependence.lean
import Mathlib
import Definitions.Def_Probability_U9DriftLocalDensity
import Definitions.Def_Probability_U9DriftLocalIndependence
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# The local conditions at distinct primes are *exactly* independent

Context (experiment 569, paper 216).  The smoothness model behind the band-9 study is
multiplicative: the chance that `j² - N` survives sieving by a set of small primes is taken
to be the product of the per-prime survival chances.  For the *local* (residue-counting)
part of that model this is not a heuristic at all — it is the Chinese remainder theorem.
This file proves it, and thereby isolates exactly which step of the Dickman-style argument
is still a heuristic (the passage from a finite prime set to full smoothness, not the
independence of the individual congruence conditions).

Main results:

* `U9Drift.chineseRemainder_fst` / `U9Drift.chineseRemainder_snd` — the CRT isomorphism is
  the pair of reduction maps, so a condition on the two components is exactly a pair of
  congruence conditions.
* `U9Drift.missCount_eq` — the number of residues `j mod p` with `p ∤ j² - N` is
  `p - (1 + legendreSym p N)`.
* `U9Drift.local_independence` — for coprime moduli the joint survivor count factors as the
  product of the two local survivor counts, with no error term.
* `U9Drift.local_independence_prod` — the same for an arbitrary finite set of pairwise
  coprime moduli: the survivor count modulo `∏ p` is `∏ (survivor count mod p)`.
* `U9Drift.missDensity_mul` — equivalently, the survival densities multiply exactly.
* `U9Drift.missDensity_eq_one_sub` / `U9Drift.missDensity_sub_control` — each factor is
  `1 - (1 + legendreSym p N)/p`, so the candidate pool's local survival probability differs
  from the control's `1 - 1/p` by exactly `legendreSym p N / p`, of either sign.
-/

open U9Drift

open Finset

/-! ## The CRT isomorphism is reduction -/

theorem chineseRemainder_fst {m n : ℕ} (h : m.Coprime n) (j : ZMod (m * n)) :
    (ZMod.chineseRemainder h j).1 = ZMod.castHom (Dvd.intro n rfl) (ZMod m) j := by
  show (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff])
    (ZMod m × ZMod n) j).1 = _
  simp [ZMod.castHom_apply, Prod.fst_zmod_cast]

theorem chineseRemainder_snd {m n : ℕ} (h : m.Coprime n) (j : ZMod (m * n)) :
    (ZMod.chineseRemainder h j).2 = ZMod.castHom (Dvd.intro_left m rfl) (ZMod n) j := by
  show (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff])
    (ZMod m × ZMod n) j).2 = _
  simp [ZMod.castHom_apply, Prod.snd_zmod_cast]

/-- Reduction is transitive: reducing mod `p` can be done in two stages through any
intermediate modulus. -/
theorem cast_cast_of_dvd {p m d : ℕ} (h1 : p ∣ m) (h2 : m ∣ d) (j : ZMod d) :
    (ZMod.cast j : ZMod p) = (ZMod.cast (ZMod.cast j : ZMod m) : ZMod p) := by
  have h := RingHom.congr_fun (ZMod.castHom_comp (n := p) (m := m) (d := d) h1 h2) j
  rw [RingHom.comp_apply, ZMod.castHom_apply, ZMod.castHom_apply, ZMod.castHom_apply] at h
  exact h.symm

/-! ## Counting the survivors at one prime -/






/-! ## Exact independence -/

/-- **Exact local independence for two coprime moduli.**  The number of residues modulo
`a·b` satisfying a condition mod `a` *and* a condition mod `b` is the product of the two
counts: the congruence conditions are exactly independent, with no error term. -/
theorem card_pair_split {a b : ℕ} (h : a.Coprime b) (P : ZMod a → Prop) (Q : ZMod b → Prop) :
    Nat.card {j : ZMod (a * b) // P (ZMod.cast j) ∧ Q (ZMod.cast j)}
      = Nat.card {x : ZMod a // P x} * Nat.card {y : ZMod b // Q y} := by
  have hfst : ∀ j : ZMod (a * b), (ZMod.chineseRemainder h j).1 = (ZMod.cast j : ZMod a) := by
    intro j; rw [chineseRemainder_fst]; simp [ZMod.castHom_apply]
  have hsnd : ∀ j : ZMod (a * b), (ZMod.chineseRemainder h j).2 = (ZMod.cast j : ZMod b) := by
    intro j; rw [chineseRemainder_snd]; simp [ZMod.castHom_apply]
  have e1 : {j : ZMod (a * b) // P (ZMod.cast j) ∧ Q (ZMod.cast j)}
      ≃ {y : ZMod a × ZMod b // P y.1 ∧ Q y.2} :=
    Equiv.subtypeEquiv (ZMod.chineseRemainder h).toEquiv (fun j => by
      rw [show ((ZMod.chineseRemainder h).toEquiv j) = ZMod.chineseRemainder h j from rfl,
        hfst j, hsnd j])
  rw [Nat.card_congr e1, Nat.card_congr (Equiv.subtypeProdEquivProd), Nat.card_prod]



/-! ## Densities -/






open U9Drift in
theorem solution(N : ℤ) :
    ∀ S : Finset ℕ, (S : Set ℕ).Pairwise Nat.Coprime → ∀ M : ℕ, M = ∏ p ∈ S, p →
      Nat.card {j : ZMod M // ∀ p ∈ S, ¬ (ZMod.cast j : ZMod p) ^ 2 = (N : ZMod p)}
        = ∏ p ∈ S, missCount p N := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _ M hM
      subst hM
      simp
  | insert a S ha ih =>
      intro hcop M hM
      rw [Finset.prod_insert ha] at hM
      subst hM
      have hcopA : a.Coprime (∏ p ∈ S, p) := by
        refine Nat.Coprime.prod_right ?_
        intro p hp
        refine hcop (by simp) (by simp [hp]) ?_
        rintro rfl
        exact ha hp
      have hcompose : ∀ (j : ZMod (a * ∏ p ∈ S, p)) (p : ℕ), p ∈ S →
          (ZMod.cast j : ZMod p)
            = (ZMod.cast (ZMod.cast j : ZMod (∏ p ∈ S, p)) : ZMod p) := by
        intro j p hp
        exact cast_cast_of_dvd (Finset.dvd_prod_of_mem _ hp) (Dvd.intro_left a rfl) j
      have hiff : ∀ j : ZMod (a * ∏ p ∈ S, p),
          (∀ p ∈ insert a S, ¬ (ZMod.cast j : ZMod p) ^ 2 = (N : ZMod p))
            ↔ ((fun x : ZMod a => ¬ x ^ 2 = (N : ZMod a)) (ZMod.cast j) ∧
              (fun y : ZMod (∏ p ∈ S, p) =>
                ∀ p ∈ S, ¬ (ZMod.cast y : ZMod p) ^ 2 = (N : ZMod p)) (ZMod.cast j)) := by
        intro j
        constructor
        · intro h
          refine ⟨h a (by simp), ?_⟩
          intro p hp
          have := h p (by simp [hp])
          rwa [hcompose j p hp] at this
        · rintro ⟨h1, h2⟩ p hp
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact h1
          · rw [hcompose j p hp']
            exact h2 p hp'
      rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),
        card_pair_split hcopA (fun x : ZMod a => ¬ x ^ 2 = (N : ZMod a))
          (fun y : ZMod (∏ p ∈ S, p) => ∀ p ∈ S, ¬ (ZMod.cast y : ZMod p) ^ 2 = (N : ZMod p)),
        ih (hcop.mono (by simp)) _ rfl, Finset.prod_insert ha]
      rfl
