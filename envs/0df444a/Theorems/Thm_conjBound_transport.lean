-- Prove2me | Theorems.Thm_conjBound_transport
-- name    : conjBound_transport
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:06:32.976657+00:00
-- url     : https://prove2.me/theorems/32be91eb-4c36-4dd0-b9af-10e3015ad73d
-- title:
--   conjBound_transport: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (with `open scoped commutatorElement IsMulCommutative Pointwise`):
--
--   ```lean
--   theorem conjBound_transport {C Q N : Type*} [Group C] [Group Q] [Group N]
--       [DecidableEq Q] [DecidableEq N]
--       {fC : C → C} {fQ : Q → Q} {fN : N → N}
--       (ψ : C →* Q) (hψ : Function.Surjective ψ) (j : C →* N) (hj : Function.Injective j)
--       (hψcomm : ∀ x, ψ (fC x) = fQ (ψ x)) (hjcomm : ∀ x, j (fC x) = fN (j x))
--       (hbound : ∀ k : ℕ, 0 < k → ∀ g : N, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
--         a < b → (Finset.image
--           (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fN^[k * ↑i] g) x.toList).prod)
--           (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q) :
--       ∀ k : ℕ, 0 < k → ∀ g : Q, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
--         a < b → (Finset.image
--           (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fQ^[k * ↑i] g) x.toList).prod)
--           (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q
--   ```
--
--   **Used by.** The proof of `GeneratesNS.theorem_3_1` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

theorem conjBound_transport {C Q N : Type*} [Group C] [Group Q] [Group N]
    [DecidableEq Q] [DecidableEq N]
    {fC : C → C} {fQ : Q → Q} {fN : N → N}
    (ψ : C →* Q) (hψ : Function.Surjective ψ) (j : C →* N) (hj : Function.Injective j)
    (hψcomm : ∀ x, ψ (fC x) = fQ (ψ x)) (hjcomm : ∀ x, j (fC x) = fN (j x))
    (hbound : ∀ k : ℕ, 0 < k → ∀ g : N, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
      a < b → (Finset.image
        (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fN^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q) :
    ∀ k : ℕ, 0 < k → ∀ g : Q, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
      a < b → (Finset.image
        (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fQ^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q := by
  sorry

end
