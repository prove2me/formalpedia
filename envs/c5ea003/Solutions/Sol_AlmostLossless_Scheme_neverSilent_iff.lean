-- Prove2me | solution 1 for AlmostLossless.Scheme.neverSilent_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:02:28.184911+00:00
-- url     : https://prove2.me/submissions/77b46454-ea4b-46a4-a800-8cd0a1fe2438

/-
# `AlmostLossless.Scheme.neverSilent_iff`
Target `731f9d3d` (Open; re-read live immediately before submitting).

ORDINARY PROOF — full closure screens CLEAN (three bundles read, no `Theorems.` import).
Gift: **SAFE**.

BINDERS — this target carries SEVEN WAs, and the published expected type shows why:
    ∀ {α : Type} {Code : Type} (sch : AlmostLossless.Scheme α Code),
      sch.NeverSilent ↔ ∀ (x : α), sch.dec (sch.enc x) = some x ∨ sch.dec (sch.enc x) = none
**NO `[Fintype α]`, NO `[DecidableEq α]`** — even though the bundle declares
`variable {α : Type*} [Fintype α]` (line 39) and `variable [DecidableEq α]` (line 87). Neither
`NeverSilent` nor `SilentError` touches them, so Lean includes neither. Seven people supplied the
section's instances; each proof compiled and each was rejected on type.

DEFINITIONS (read from the bundle):
    Scheme.Succeeds sch x     = sch.dec (sch.enc x) = some x
    Scheme.SilentError sch x  = ∃ y, sch.dec (sch.enc x) = some y ∧ y ≠ x
    Scheme.NeverSilent sch    = ∀ x, ¬ sch.SilentError x

MATHS. "Never silently corrupts" means every confident answer is right; equivalently the decoder
either answers correctly or abstains. The proof is a case split on `sch.dec (sch.enc x)`:
  * `none`  — the decoder abstained, so the right disjunct holds and there is no witness to corrupt;
  * `some z` — a silent error would be exactly a witness `z ≠ x`, so its absence forces `z = x`.
Both directions are that observation read in opposite order; no arithmetic, no finiteness — which is
precisely why the instances are absent from the expected type.
-/
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlmostLossless

open AlmostLossless in
/-- **The target, verbatim.** -/
theorem solution {α : Type*} {Code : Type*} (sch : Scheme α Code) :
    sch.NeverSilent ↔ ∀ x, sch.dec (sch.enc x) = some x ∨ sch.dec (sch.enc x) = none := by
  constructor
  · intro h x
    cases hd : sch.dec (sch.enc x) with
    | none => exact Or.inr rfl
    | some z =>
        left
        by_cases hz : z = x
        · exact congrArg some hz
        · exact absurd (show sch.SilentError x from ⟨z, hd, hz⟩) (h x)
  · intro h x hse
    obtain ⟨y, hy, hyx⟩ := hse
    rcases h x with hc | hc
    · rw [hc] at hy
      exact hyx (Option.some_inj.mp hy).symm
    · rw [hc] at hy
      simp at hy
