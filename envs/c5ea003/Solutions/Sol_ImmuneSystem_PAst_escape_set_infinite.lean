-- Prove2me | solution 1 for ImmuneSystem.PAst.escape_set_infinite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:30:37.964739+00:00
-- url     : https://prove2.me/submissions/d5276cb4-5d5b-476b-b621-1696bfb7a2e6

-- Sol generated from Shared/ImmuneDetection.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneDetection
import Definitions.Def_Shared_ImmuneSemantics
import Theorems.Thm_ImmuneSystem_PAst_pad_injective
import Theorems.Thm_ImmuneSystem_PAst_sound_detector_misses

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









theorem parasite_injective (d : PAst) : Function.Injective (parasite d) := by
  intro l l' h
  simp only [parasite, PAst.ite.injEq] at h
  exact pad_injective h.2.1










/-! ### Non-vacuity and sharpness of the dichotomy

The impossibility theorem is not vacuous: harmless detectors exist in abundance,
and each of the two requirements (soundness, completeness) is separately
achievable.  Only their conjunction is impossible. -/











open ImmuneSystem.PAst in
theorem solution{d : PAst} (hd : IsPure d) (hs : Sound d) :
    {t : PAst | malicious t ∧ ¬ Flags d t}.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => parasite d (List.replicate n true)) := by
    intro m n h
    have := parasite_injective d h
    simpa using congrArg List.length this
  have hmaps : Set.range (fun n : ℕ => parasite d (List.replicate n true))
      ⊆ {t : PAst | malicious t ∧ ¬ Flags d t} := by
    rintro t ⟨n, rfl⟩
    exact sound_detector_misses hd hs _
  exact Set.Infinite.mono hmaps (Set.infinite_range_of_injective hinj)
