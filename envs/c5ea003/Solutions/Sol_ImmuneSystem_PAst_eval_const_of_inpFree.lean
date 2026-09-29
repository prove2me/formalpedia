-- Prove2me | solution 1 for ImmuneSystem.PAst.eval_const_of_inpFree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:27:28.763591+00:00
-- url     : https://prove2.me/submissions/f6fa1b66-37e5-4c99-91ac-03b6d14c71c4

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










@[simp] theorem inpFree_inp : inpFree inp = false := rfl
@[simp] theorem inpFree_ite (c a b : PAst) :
    inpFree (ite c a b) = (inpFree c && inpFree a && inpFree b) := rfl
@[simp] theorem inpFree_call (f a : PAst) :
    inpFree (call f a) = (inpFree f && inpFree a) := rfl
@[simp] theorem eval_lit (n x : ℕ) : eval (lit n) x = n := rfl
@[simp] theorem eval_ite (c a b : PAst) (x : ℕ) :
    eval (ite c a b) x = if eval c x ≠ 0 then eval a x else eval b x := rfl
@[simp] theorem eval_call (f a : PAst) (x : ℕ) : eval (call f a) x = eval f (eval a x) := rfl

open ImmuneSystem.PAst in
theorem solution:
    ∀ {t : PAst}, inpFree t = true → ∀ x y : ℕ, eval t x = eval t y := by
  intro t
  induction t with
  | inp => intro h; simp at h
  | attack => intro _ x y; rfl
  | lit n => intro _ x y; rfl
  | ite c a b ihc iha ihb =>
      intro h x y
      simp only [inpFree_ite, Bool.and_eq_true] at h
      obtain ⟨⟨hc, ha⟩, hb⟩ := h
      simp only [eval_ite, ihc hc x y, iha ha x y, ihb hb x y]
  | call f a ihf iha =>
      intro h x y
      simp only [inpFree_call, Bool.and_eq_true] at h
      obtain ⟨hf, ha⟩ := h
      simp only [eval_call, iha ha x y]
