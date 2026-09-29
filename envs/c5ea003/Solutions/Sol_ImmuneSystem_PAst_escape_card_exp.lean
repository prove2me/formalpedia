-- Prove2me | solution 1 for ImmuneSystem.PAst.escape_card_exp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:30:36.508213+00:00
-- url     : https://prove2.me/submissions/fbbb227e-7820-4f0c-bce1-a51af138a758

-- Sol generated from Shared/ImmuneDetection.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneDetection
import Definitions.Def_Shared_ImmuneSemantics
import Theorems.Thm_ImmuneSystem_PAst_pad_injective
import Theorems.Thm_ImmuneSystem_PAst_size_pad
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








@[simp] theorem size_lit (n : ℕ) : size (lit n) = 1 := rfl
@[simp] theorem size_inp : size inp = 1 := rfl
@[simp] theorem size_attack : size attack = 1 := rfl
@[simp] theorem size_ite (c a b : PAst) :
    size (ite c a b) = 1 + size c + size a + size b := rfl
@[simp] theorem size_call (f a : PAst) : size (call f a) = 1 + size f + size a := rfl

theorem size_parasite (d : PAst) (l : List Bool) :
    size (parasite d l) = size d + 3 * l.length + 5 := by
  simp [parasite, size_pad]
  omega

theorem parasite_injective (d : PAst) : Function.Injective (parasite d) := by
  intro l l' h
  simp only [parasite, PAst.ite.injEq] at h
  exact pad_injective h.2.1










/-! ### Non-vacuity and sharpness of the dichotomy

The impossibility theorem is not vacuous: harmless detectors exist in abundance,
and each of the two requirements (soundness, completeness) is separately
achievable.  Only their conjunction is impossible. -/











open ImmuneSystem.PAst in
theorem solution{d : PAst} (hd : IsPure d) (hs : Sound d) (n : ℕ) :
    ∃ S : Finset PAst, S.card = 2 ^ n ∧
      ∀ t ∈ S, malicious t ∧ ¬ Flags d t ∧ size t ≤ size d + 3 * n + 5 := by
  classical
  refine ⟨Finset.image (fun v : Fin n → Bool => parasite d (List.ofFn v)) Finset.univ, ?_, ?_⟩
  · have hinj : Function.Injective (fun v : Fin n → Bool => parasite d (List.ofFn v)) :=
      Function.Injective.comp (parasite_injective d) List.ofFn_injective
    rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro t ht
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨v, rfl⟩ := ht
    obtain ⟨h1, h2⟩ := sound_detector_misses hd hs (List.ofFn v)
    refine ⟨h1, h2, ?_⟩
    rw [size_parasite]
    simp
