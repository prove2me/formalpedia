-- Prove2me | solution 1 for ImmuneSystem.PAst.pad_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:12:56.034636+00:00
-- url     : https://prove2.me/submissions/d84bffc4-f1fc-4a0e-9c2b-8ddefa7644af

-- Sol generated from Shared/ImmuneSemantics.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneSemantics

/-!
# Algorithmic Immune System, Part II: semantics, effects and self-execution

We equip the parasite calculus of Part I with a *total* denotational semantics
consisting of two layers:

* `PAst.eval t x` — the value computed by `t` when its input register holds `x`;
* `PAst.effect t x` — whether running `t` on input `x` *executes the forbidden
  action* `attack` (only the branch actually taken counts, so dead code is truly
  dead).

The runtime is *self-referential*: a program is always run on its own
attestation tag (`PAst.run t = PAst.effect t (PAst.code t)`), which is exactly
the ability of real self-modifying code to inspect its own source.  A program is
`malicious` when its self-execution performs the forbidden action.

Main results:

* `PAst.eval_const_of_inpFree` / `PAst.effect_const_of_inpFree`: programs without
  the self register are input-oblivious;
* `PAst.staticScan_correct`: the naive static scanner
  `staticScan t = effect t 0` is **sound and complete** on self-reference-free
  programs — the immune system wins outright in the absence of quining;
* `PAst.malicious_decidable_of_inpFree`: consequently maliciousness is decidable
  there.

Part III shows that both properties fail, unavoidably, once the self register is
available.
-/

open ImmuneSystem
open PAst














/-! ### A benign padding family

`pad` is an exponentially large family of *semantically identical* benign
programs (all compute `0`, none has any effect).  It is the raw material both for
the immune-escape counting theorem of Part III and for the false-positive
counting theorem of Part IV. -/










open ImmuneSystem.PAst in
theorem solution: Function.Injective pad := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l' with
      | nil => rfl
      | cons b bs => simp [pad] at h
  | cons b bs ih =>
      intro l' h
      cases l' with
      | nil => simp [pad] at h
      | cons b' bs' =>
          simp only [pad, PAst.ite.injEq, PAst.lit.injEq] at h
          obtain ⟨-, hb, hbs⟩ := h
          have : b = b' := by
            by_cases hb1 : b <;> by_cases hb2 : b' <;> simp [hb1, hb2] at hb ⊢
          rw [this, ih hbs]
