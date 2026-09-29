-- Prove2me | Definitions.Def_Shared_ImmuneDetection
-- name    : Shared_ImmuneDetection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:57:24.058146+00:00
-- url     : https://prove2.me/theorems/16e033b3-08d2-48d7-b1f6-49bef3328f17
-- title:
--   Aether Catalog definitions — Shared_ImmuneDetection
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ImmuneDetection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ImmuneDetection.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
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

namespace ImmuneSystem
namespace PAst

/-- A detector program is *pure* if running it never triggers the forbidden
action: the immune system must not itself be a parasite. -/
def IsPure (d : PAst) : Prop := ∀ x : ℕ, effect d x = false

/-- The verdict of detector `d` on program `t`: `d` is run on the attestation tag
of `t` and accuses `t` iff it returns a nonzero value. -/
def Flags (d t : PAst) : Prop := eval d (code t) ≠ 0

/-- No false alarms. -/
def Sound (d : PAst) : Prop := ∀ t : PAst, Flags d t → malicious t

/-- No missed attacks. -/
def Complete (d : PAst) : Prop := ∀ t : PAst, malicious t → Flags d t



/-- The **diagonal parasite** with benign padding `l`: it consults the detector on
its own attestation tag and attacks exactly when the detector clears it. -/
def parasite (d : PAst) (l : List Bool) : PAst := ite (call d inp) (pad l) attack












/-! ### Non-vacuity and sharpness of the dichotomy

The impossibility theorem is not vacuous: harmless detectors exist in abundance,
and each of the two requirements (soundness, completeness) is separately
achievable.  Only their conjunction is impossible. -/










end PAst
end ImmuneSystem


