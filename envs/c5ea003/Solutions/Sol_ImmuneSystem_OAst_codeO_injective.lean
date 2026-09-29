-- Prove2me | solution 1 for ImmuneSystem.OAst.codeO_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:11:26.267715+00:00
-- url     : https://prove2.me/submissions/867bc1cf-c9ad-4c03-8199-91177fa3a156

-- Sol generated from Shared/ImmuneOracle.lean
import Mathlib
import Definitions.Def_Shared_ImmuneOracle
import Definitions.Def_Shared_ImmuneQuarantine

/-!
# Algorithmic Immune System, Part V: the reflexive oracle barrier

Part III proved that no *program* of the parasite calculus can be a sound and
complete behavioural detector.  A natural objection is that this might be a
limitation of computational power: perhaps a sufficiently strong immune system —
one with unbounded, even hypercomputational, analysis capability — could succeed.

Here we refute that objection in the strongest possible form.  We extend the
calculus with a primitive `ask` that queries an **arbitrary function**
`O : ℕ → ℕ` (the immune oracle: no computability whatsoever is assumed) on a
computed attestation tag, and we let programs use it freely.  Then:

* `no_correct_reflexive_oracle` — **for every** `O : ℕ → ℕ` there is a program
  whose behaviour `O` misdescribes.  Reflexivity, not computational power, is the
  barrier;
* `askFree_eval_oracle_indep`, `askFree_effect_oracle_indep` — programs that do
  not consult the immune system have oracle-independent behaviour;
* `oracle_correct_on_askFree` — and for those programs a correct (noncomputably
  defined) oracle *does* exist.

Together (`reflexive_dichotomy`) this locates the exact frontier: an immune
system can be perfectly correct about code that ignores it, and is necessarily
wrong about code that watches it.
-/

open ImmuneSystem


open OAst




variable (O : ℕ → ℕ)



















@[simp] theorem codeO_lit (n : ℕ) : codeO (lit n) = 5 * n + 2 := rfl
@[simp] theorem codeO_ite (c a b : OAst) :
    codeO (ite c a b) = 5 * (Nat.pair (Nat.pair (codeO c) (codeO a)) (codeO b)) + 3 := rfl
@[simp] theorem codeO_ask (a : OAst) : codeO (ask a) = 5 * codeO a + 4 := rfl

open ImmuneSystem.OAst in
theorem solution: Function.Injective codeO := by
  intro s
  induction s with
  | inp => intro t h; cases t <;> simp_all [codeO]
  | attack => intro t h; cases t <;> simp_all [codeO]
  | lit n =>
      intro t h
      cases t with
      | lit m => simp only [codeO_lit] at h; simp; omega
      | _ => simp_all [codeO] <;> omega
  | ite c a b ihc iha ihb =>
      intro t h
      cases t with
      | ite c' a' b' =>
          simp only [codeO_ite] at h
          have hp : Nat.pair (Nat.pair (codeO c) (codeO a)) (codeO b)
              = Nat.pair (Nat.pair (codeO c') (codeO a')) (codeO b') := by omega
          rw [Nat.pair_eq_pair, Nat.pair_eq_pair] at hp
          obtain ⟨⟨h1, h2⟩, h3⟩ := hp
          rw [ihc h1, iha h2, ihb h3]
      | _ => simp_all [codeO] <;> omega
  | ask a iha =>
      intro t h
      cases t with
      | ask a' =>
          simp only [codeO_ask] at h
          rw [iha (by omega : codeO a = codeO a')]
      | _ => simp_all [codeO] <;> omega
