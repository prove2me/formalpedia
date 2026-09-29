-- Prove2me | solution 1 for Transreal.fin_div_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T06:13:54.175042+00:00
-- url     : https://prove2.me/submissions/5506ba98-4892-4894-9420-8df2db591939

/-
# `Transreal.fin_div_self`
Target `230aafcf` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.
Same bundle as the already-shipped `62a16eee`, so it is fetched, built, and its clause order known.

    div a b = a * recip b
    recip (fin x) = if x = 0 then pinf else fin x⁻¹
    mul (fin x) pinf = if x = 0 then null else if 0 < x then pinf else ninf
    mul (fin x) (fin y) = fin (x * y)

Claim: `fin x / fin x = if x = 0 then null else fin 1`.

  x = 0 : recip gives `pinf`, so this is `mul (fin 0) pinf`, whose own guard `if x = 0`
          returns `null`.
  x ≠ 0 : recip gives `fin x⁻¹`, so this is `fin (x * x⁻¹) = fin 1`, needing only that a
          nonzero real times its inverse is one.

CLAUSE-ORDER CAUTION, the same one that made `62a16eee` compile first try: `fin, pinf` is the
FOURTH clause of `mul`, reached only after three earlier patterns fail to match, so the `x = 0`
branch is not reflexivity on the nose — the inner `if x = 0` still has to be evaluated.
-/
import Mathlib
import Definitions.Def_Cryptography_Transreal_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open Transreal in
/-- **The target, verbatim.** -/
theorem solution (x : ℝ) : fin x / fin x = if x = 0 then null else fin 1 := by
  show Transreal.mul (Transreal.fin x) (Transreal.recip (Transreal.fin x)) = _
  by_cases hx : x = 0
  · subst hx
    simp [Transreal.recip, Transreal.mul]
  -- the linter confirmed `mul_inv_cancel₀ hx` was never used: simp finds the
  -- inverse cancellation itself once `hx : x ≠ 0` is in the simp set.
  · simp [Transreal.recip, Transreal.mul, hx]
