-- Prove2me | Definitions.Def_Erdos249257_TotientTailPeriodKiller
-- name    : Erdos249257_TotientTailPeriodKiller
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:43:37.192165+00:00
-- url     : https://prove2.me/theorems/bbae040c-74f7-4661-baff-0fe67daf481d
-- title:
--   Totient-window discrepancy and period-avoidance certificate
-- statement:
--   This bundle defines an integer totient-window discrepancy, a decidable certificate requiring its residue modulo 2^L to avoid an explicit neighborhood of zero, and the certificate’s decidability instance.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientTailPeriodKiller.lean#L1-L422
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The totient-tail period killer: attacking #249 through the period, not the digits

Every earlier wave asked the Erdős–Borwein question of `S = ∑ φ(n)/2ⁿ`: force a
long block of zero binary digits.  Wave 20 measured why that fails — the
totient's 2-adic staircase affords `√(2·log₂ N)` silent positions where the
proof engine needs `log₂ N`.  This file changes the TARGET.  Rationality of `S`
is equivalent to *eventual periodicity* of its binary expansion, and
periodicity is a statement about the local totient tail

  `R_N = ∑_{j≥1} φ(N+j)/2ʲ`,      because `2^N·S = Φ_N + R_N` with `Φ_N ∈ ℕ`.

If `S = P/Q` then for `h` with `oddPart Q ∣ 2ʰ - 1` and every `N ≥ v₂(Q)`,

  `R_{N+h} - R_N ∈ ℤ`   —   the **tail-period law**.

Killing a period is a FINITE, decidable act.  With the window discrepancy

  `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`

we get `R_{N+h} - R_N = A/2^L + E`, `|E| ≤ (N+h+L+2)/2^L`, so whenever the
residue `A mod 2^L` lands outside the radius-`(N+h+L+2)` neighbourhood of `0`,
the difference is provably NOT an integer (`tail_diff_notMem_int_of_certifiedKill`).
The forbidden zone has width `O(N)` inside a modulus `2^L ≈ N³`: the old proof
had to HIT a measure-zero target, this one only has to MISS a vanishing one.

The reduction is complete (`irrational_totient_series_of_certificate_supply`):
a supply of certified kills — for every period `h` and every threshold `N₀`
some certified `(N ≥ N₀, L)` — proves #249.  As a first unconditional deposit,
`certifiedKill_all_small` machine-checks kills for every `h ≤ 8` at `N = 12`,
`L = 16`, so `S` is not a rational whose denominator divides `2¹²·(2ʰ-1)` for
any `h ≤ 8` (`totient_series_ne_rat_of_den_dvd`).

Everything here is elementary: `φ(n) ≤ n`, geometric tails, and integer
window arithmetic.  No q-Padé, no Stern–Brocot, no unformalised citations.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset





/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`:
the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. -/
def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L`
avoids the radius-`(N+h+L+2)` neighbourhood of `0`. -/
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)



instance (h N L : ℕ) : Decidable (certifiedKill h N L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Geometric-linear summability spine -/













/-! ## The shift identity: `2^N · S = Φ_N + R_N` -/



/-! ## Truncation: partial window plus bounded tail -/







/-! ## Certificate soundness: a good residue kills integrality -/





/-! ## Rationality forces the tail-period law -/





/-! ## The reduction, and the first unconditional deposits -/









end TotientTailPeriodKiller
end Erdos249257


