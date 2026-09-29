-- Prove2me | solution 1 for ScanSchemeDecoding.constScheme_decodeCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:03:59.464187+00:00
-- url     : https://prove2.me/submissions/04571f19-cf40-4e2b-ba03-47b876949ab9

-- Sol generated from Algebra/ScanSchemeDecoding/Spectrum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Spectrum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq

/-!
# The cost spectrum of scan schemes

The exact optimum pins down the *bottom* of the achievable total-cost spectrum.  Here we
pin down the *top*: the triangular number `triangle N` of the whole key set, attained by
the degenerate one-bucket scheme.  The mechanism is the exact opposite of convexity used
for the optimum, namely superadditivity `triangle a + triangle b ≤ triangle (a + b)`.

## Main results

* `ScanSchemeDecoding.triangle_add_le` — superadditivity of the triangular cost.
* `ScanSchemeDecoding.sum_triangle_le` — a scan scheme never costs more than a single
  linear scan of all keys.
* `ScanSchemeDecoding.scan_maximum` — `triangle N` is the greatest achievable cost.
* `ScanSchemeDecoding.scan_cost_spectrum` — every scan scheme on `N` keys with `m > 0`
  buckets has total cost in the closed interval `[triangleOpt N m, triangle N]`, and both
  endpoints are realised.
-/

open ScanSchemeDecoding

open Finset



open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)








open ScanSchemeDecoding in
theorem solution(N : ℕ) {m : ℕ} (b₀ : Fin m) :
    ∑ x, (constScheme N b₀).decodeCost x = triangle N := by
  classical
  rw [ScanScheme.decodeCost_eq]
  rw [Finset.sum_eq_single b₀]
  · congr 1
    have : (constScheme N b₀).fiber b₀ = Finset.univ := by
      ext x; simp [ScanScheme.fiber, constScheme]
    rw [this]
    simp
  · intro b _ hb
    have hempty : (constScheme N b₀).fiber b = ∅ := by
      ext x
      simp [ScanScheme.fiber, constScheme, Ne.symm hb]
    rw [hempty]
    simp [triangle]
  · intro h
    exact absurd (Finset.mem_univ b₀) h
