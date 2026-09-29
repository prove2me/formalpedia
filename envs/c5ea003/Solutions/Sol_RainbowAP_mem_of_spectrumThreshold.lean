-- Prove2me | solution 1 for RainbowAP.mem_of_spectrumThreshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:22:11.429847+00:00
-- url     : https://prove2.me/submissions/ecd546ec-08e9-447c-ae9f-2922cd29180d

-- Sol generated from Shared/RainbowAPSpectrumThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Definitions.Def_Shared_RainbowAPSpectrumThreshold

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

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]













open RainbowAP in
lemma solution(hne : {m | 2 * nonSurjCount α m < Fintype.card α ^ m}.Nonempty) :
    2 * nonSurjCount α (spectrumThreshold α) < Fintype.card α ^ (spectrumThreshold α) :=
  Nat.sInf_mem hne
