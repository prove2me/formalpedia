-- Prove2me | solution 1 for ImmuneSystem.OAst.askFree_eval_oracle_indep
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:24:01.2316+00:00
-- url     : https://prove2.me/submissions/59e01bb0-2251-4324-a055-0e8f7fdbe56d

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



















@[simp] theorem askFree_ite (c a b : OAst) :
    askFree (ite c a b) = (askFree c && askFree a && askFree b) := rfl
@[simp] theorem askFree_ask (a : OAst) : askFree (ask a) = false := rfl
@[simp] theorem evalO_ite (c a b : OAst) (x : ℕ) :
    evalO O (ite c a b) x = if evalO O c x ≠ 0 then evalO O a x else evalO O b x := rfl

open ImmuneSystem.OAst in
theorem solution:
    ∀ {t : OAst}, askFree t = true → ∀ (O O' : ℕ → ℕ) (x : ℕ), evalO O t x = evalO O' t x := by
  intro t
  induction t with
  | inp => intro _ O O' x; rfl
  | attack => intro _ O O' x; rfl
  | lit n => intro _ O O' x; rfl
  | ite c a b ihc iha ihb =>
      intro h O O' x
      simp only [askFree_ite, Bool.and_eq_true] at h
      obtain ⟨⟨hc, ha⟩, hb⟩ := h
      simp only [evalO_ite, ihc hc O O' x, iha ha O O' x, ihb hb O O' x]
  | ask a _ => intro h; simp at h
