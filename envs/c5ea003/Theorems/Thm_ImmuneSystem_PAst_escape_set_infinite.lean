-- Prove2me | Theorems.Thm_ImmuneSystem_PAst_escape_set_infinite
-- name    : ImmuneSystem.PAst.escape_set_infinite
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:43:57.631267+00:00
-- url     : https://prove2.me/theorems/ad13e006-f0f2-4fbf-a3c1-fb38d5bca733
-- title:
--   Immune escape is infinite.
-- statement:
--   **Immune escape is infinite.**  A harmless detector without false alarms
--   misses infinitely many genuinely malicious programs.
--
--   ```lean
--   theorem ImmuneSystem.PAst.escape_set_infinite{d : PAst} (hd : IsPure d) (hs : Sound d) :
--       {t : PAst | malicious t ∧ ¬ Flags d t}.Infinite := by sorry
--
--
--   /-! ### Non-vacuity and sharpness of the dichotomy
--
--   The impossibility theorem is not vacuous: harmless detectors exist in abundance,
--   and each of the two requirements (soundness, completeness) is separately
--   achievable.  Only their conjunction is impossible. -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneDetection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneDetection.lean#L126

-- Thm stub generated from Shared/ImmuneDetection.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneDetection
import Definitions.Def_Shared_ImmuneSemantics

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

theorem ImmuneSystem.PAst.escape_set_infinite{d : PAst} (hd : IsPure d) (hs : Sound d) :
    {t : PAst | malicious t ∧ ¬ Flags d t}.Infinite := by sorry
