-- Prove2me | solution 1 for ImmuneSystem.OAst.oracle_correct_on_askFree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:12:55.431304+00:00
-- url     : https://prove2.me/submissions/4fe756c5-2bc1-43b1-b669-b6ea5c6ee359

-- Sol generated from Shared/ImmuneOracle.lean
import Mathlib
import Definitions.Def_Shared_ImmuneOracle
import Definitions.Def_Shared_ImmuneQuarantine
import Theorems.Thm_ImmuneSystem_OAst_askFree_effect_oracle_indep
import Theorems.Thm_ImmuneSystem_OAst_codeO_injective

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














/-- Maliciousness of non-reflexive programs does not depend on the oracle. -/
theorem maliciousO_oracle_indep {t : OAst} (h : askFree t = true) (O O' : ℕ → ℕ) :
    maliciousO O t ↔ maliciousO O' t := by
  unfold maliciousO
  rw [askFree_effect_oracle_indep h O O' (codeO t)]





open ImmuneSystem.OAst in
theorem solution:
    ∃ O : ℕ → ℕ, ∀ (O' : ℕ → ℕ) (t : OAst), askFree t = true →
      (O (codeO t) ≠ 0 ↔ maliciousO O' t) := by
  classical
  refine ⟨canonicalOracle, ?_⟩
  intro O' t ht
  unfold canonicalOracle
  by_cases hmal : maliciousO (fun _ => 0) t
  · have hex : ∃ s : OAst, codeO s = codeO t ∧ askFree s = true
        ∧ maliciousO (fun _ => 0) s := ⟨t, rfl, ht, hmal⟩
    simp only [hex, if_true]
    exact ⟨fun _ => (maliciousO_oracle_indep ht _ O').1 hmal, fun _ => one_ne_zero⟩
  · have hex : ¬ ∃ s : OAst, codeO s = codeO t ∧ askFree s = true
        ∧ maliciousO (fun _ => 0) s := by
      rintro ⟨s, hs, _, hsm⟩
      exact hmal (codeO_injective hs ▸ hsm)
    simp only [hex, if_false]
    constructor
    · intro hne; exact absurd rfl hne
    · intro hm
      exact absurd ((maliciousO_oracle_indep ht O' (fun _ => 0)).1 hm) hmal
