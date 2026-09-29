-- Prove2me | solution 1 for Cryptography.WeilBLS.WeilPairing.pair_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:38:43.4472+00:00
-- url     : https://prove2.me/submissions/77453124-3b86-40de-8a4c-e2d1dc119086

/-
Target for `Cryptography.WeilBLS.WeilPairing`. No WA exists on these (CE x4), so the binder list is
read from the bundle: file-level `variable {F} [Field F] [DecidableEq F]` plus, inside
`namespace WeilPairing`, `{W} {n} {μ} [CommGroup μ] (e : WeilPairing W n μ)`.

The pairing's laws are FIELDS of the structure — `alternating : ∀ P, hom P P = 0` — and
`pair P Q = Additive.toMul (e.hom P Q)`, so these are field lookups, not theorems to build.

NOTE: `Type*`, not `Type u`. The probe compiled with autoImplicit auto-binding `u`/`v`, but the
generated GATE cannot express those, and preflight failed with "unknown universe level".
-/
import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS

set_option maxHeartbeats 400000

open Cryptography.WeilBLS Finset

open Cryptography.WeilBLS in
/-- **The target, verbatim.** -/
theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {n : ℕ}
    {μ : Type*} [CommGroup μ] (e : WeilPairing W n μ) (P : torsionPoints W n) :
    e.pair P 0 = 1 := by
  simp [WeilPairing.pair]
