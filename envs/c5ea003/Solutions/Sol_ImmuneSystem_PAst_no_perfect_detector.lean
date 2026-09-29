-- Prove2me | solution 1 for ImmuneSystem.PAst.no_perfect_detector
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:30:42.65196+00:00
-- url     : https://prove2.me/submissions/804e50c2-b46c-41c1-856d-2fb4d5b2e0cd

-- Sol generated from Shared/ImmuneDetection.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneDetection
import Definitions.Def_Shared_ImmuneSemantics
import Theorems.Thm_ImmuneSystem_PAst_effect_pad

/-!
# Algorithmic Immune System, Part III: the diagonal parasite and immune escape

This is the adversarial heart of the development.  A *behavioural detector* is a
program `d` of the parasite calculus which is itself harmless (`IsPure`) and
which, given the attestation tag of a program, returns a nonzero verdict exactly
on the programs it accuses (`Flags`).  Soundness = no false alarms, completeness
= no missed attacks.

We construct, for every pure detector `d`, the **diagonal parasite**

```
parasite d l = ite (call d inp) (pad l) attack
```

which feeds its own attestation tag to the detector and attacks precisely when it
is cleared.  From the single lemma `malicious_parasite_iff` we derive:

* `no_perfect_detector`    — no pure detector is both sound and complete
  (a Cohen/Rice-style undecidability of virus detection, fully formalised);
* `detector_dilemma`       — every pure detector has an explicit adversarial
  witness on which it errs;
* `sound_detector_misses`  / `complete_detector_false_alarms` — the two horns;
* `escape_set_infinite`    — a sound detector misses *infinitely many* genuinely
  malicious programs;
* `escape_card_exp`        — quantitatively: at least `2 ^ n` missed attacks of
  size at most `size d + 3n + 5`, i.e. the immune escape set has exponential
  density in program size;
* `immune_dichotomy`       — the boundary: detection is perfectly solvable on
  self-reference-free code (`staticScan`) and unsolvable in general.  Quining is
  exactly the source of the undecidability.
-/

open ImmuneSystem
open PAst





@[simp] theorem eval_inp (x : ℕ) : eval inp x = x := rfl
@[simp] theorem eval_attack (x : ℕ) : eval attack x = 1 := rfl
@[simp] theorem eval_lit (n x : ℕ) : eval (lit n) x = n := rfl
@[simp] theorem eval_ite (c a b : PAst) (x : ℕ) :
    eval (ite c a b) x = if eval c x ≠ 0 then eval a x else eval b x := rfl
@[simp] theorem eval_call (f a : PAst) (x : ℕ) : eval (call f a) x = eval f (eval a x) := rfl
@[simp] theorem effect_inp (x : ℕ) : effect inp x = false := rfl
@[simp] theorem effect_attack (x : ℕ) : effect attack x = true := rfl
@[simp] theorem effect_lit (n x : ℕ) : effect (lit n) x = false := rfl
@[simp] theorem effect_ite (c a b : PAst) (x : ℕ) :
    effect (ite c a b) x = (effect c x || (if eval c x ≠ 0 then effect a x else effect b x)) := rfl
@[simp] theorem effect_call (f a : PAst) (x : ℕ) :
    effect (call f a) x = (effect a x || effect f (eval a x)) := rfl

/-- Running a pure detector on the self register has no effect and returns the
detector's verdict on the current input. -/
theorem effect_call_pure {d : PAst} (hd : IsPure d) (x : ℕ) :
    effect (call d inp) x = false := by
  simp [hd x]

/-- **Generic diagonal branch.**  For a pure detector `d`, the program that asks
`d` about its own code and then runs `A` (if accused) or `B` (if cleared) has
exactly the effect of the branch selected by the detector's verdict. -/
theorem effect_diagonal {d : PAst} (hd : IsPure d) (A B : PAst) (x : ℕ) :
    effect (ite (call d inp) A B) x = if eval d x ≠ 0 then effect A x else effect B x := by
  simp [effect_call_pure hd]





/-- **The diagonal identity.**  A parasite attacks precisely when the detector
fails to flag it. -/
theorem malicious_parasite_iff {d : PAst} (hd : IsPure d) (l : List Bool) :
    malicious (parasite d l) ↔ ¬ Flags d (parasite d l) := by
  unfold malicious run Flags parasite
  rw [effect_diagonal hd]
  simp








/-! ### Non-vacuity and sharpness of the dichotomy

The impossibility theorem is not vacuous: harmless detectors exist in abundance,
and each of the two requirements (soundness, completeness) is separately
achievable.  Only their conjunction is impossible. -/











open ImmuneSystem.PAst in
theorem solution: ¬ ∃ d : PAst, IsPure d ∧ Sound d ∧ Complete d := by
  rintro ⟨d, hd, hs, hc⟩
  by_cases h : Flags d (parasite d [])
  · have hmal : malicious (parasite d []) := hs _ h
    exact ((malicious_parasite_iff hd []).1 hmal) h
  · have hmal : malicious (parasite d []) := (malicious_parasite_iff hd []).2 h
    exact h (hc _ hmal)
