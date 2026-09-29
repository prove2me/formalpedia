-- Prove2me | Definitions.Def_Shared_RainbowAPSpectrumThreshold
-- name    : Shared_RainbowAPSpectrumThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:12:21.803832+00:00
-- url     : https://prove2.me/theorems/824af27c-389f-4154-89e3-5c3edc0d4106
-- title:
--   Aether Catalog definitions — Shared_RainbowAPSpectrumThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.RainbowAPSpectrumThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/RainbowAPSpectrumThreshold.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

/-!
# The full-spectrum (coupon-collector) threshold for words over a finite alphabet

For a finite alphabet `α` with `N = |α|` letters, a word `f : Fin m → α` has *full spectrum*
if it is surjective, i.e. every letter of `α` occurs.  We study the counting threshold

  `spectrumThreshold α = least m such that a strict majority of the `N ^ m` words of length `m`
   have full spectrum`.

The two criteria proved here are purely arithmetic and come from the first and second moment
identities of `Shared.RainbowAPSpectrumMoments`:

* if `2 * N * (N-1)^m < N^m` then the majority is surjective (union bound / first moment);
* if `N^m < (N+1) * (N-1)^m` then the majority is **not** surjective
  (Cauchy–Schwarz / second moment).

Both criteria are sharp up to the additive constants inside the logarithm, which is what makes
the resulting threshold asymptotically `N log N`.
-/

open Finset

namespace RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The words of length `m` over `α` which miss at least one letter. -/
def nonSurjSet (α : Type*) [Fintype α] [DecidableEq α] (m : ℕ) : Finset (Fin m → α) :=
  (univ : Finset (Fin m → α)).filter (fun f => 0 < missCount f)

/-- The number of words of length `m` over `α` which miss at least one letter. -/
def nonSurjCount (α : Type*) [Fintype α] [DecidableEq α] (m : ℕ) : ℕ :=
  (nonSurjSet α m).card







/-- The full-spectrum threshold of an alphabet: the least word length at which a strict majority
of words uses every letter. -/
noncomputable def spectrumThreshold (α : Type*) [Fintype α] [DecidableEq α] : ℕ :=
  sInf {m | 2 * nonSurjCount α m < Fintype.card α ^ m}



end RainbowAP


