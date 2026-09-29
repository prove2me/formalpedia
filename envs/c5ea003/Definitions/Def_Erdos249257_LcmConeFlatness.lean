-- Prove2me | Definitions.Def_Erdos249257_LcmConeFlatness
-- name    : Erdos249257_LcmConeFlatness
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:51:42.094729+00:00
-- url     : https://prove2.me/theorems/6aa16d21-9242-445c-af9d-7f076e39c435
-- title:
--   Two-window discrepancy and rank-two boundary certificate
-- statement:
--   This bundle defines a second window-discrepancy from two shifted windows and a decidable rank-two certificate requiring its residue modulo 2^L to lie outside two explicit boundary intervals.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/LcmConeFlatness.lean#L1-L650
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
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
# Wave 24: the lcm-cone flatness law and the annihilator calculus

Wave 23 collapsed #249 onto one decidable sequence: `P t := ∃ L,
certifiedKill (H_t, H_t, L)` with `H_t = lcm(1..t)`.  This file spends the
rationality hypothesis ALL the way.

**1. The cone flatness law.**  Rationality does not merely constrain the
diagonal pair `(H_t, 2H_t)`: it forces ONE fractional constant on the entire
lcm cone `{k·H_t : k ≥ 1}`.  Once `t ≥ h₀` and `q·H_t ≥ N₀`, every difference
`R_{(q+m)H_t} - R_{qH_t}` is an integer
(`rational_totient_series_forces_lcm_cone_flatness`).  Since
`periodLcm t ∣ periodLcm u` for `t ≤ u` (`periodLcm_dvd_periodLcm`), the
cones at all scales form one directed system: every cross-scale pair
`(q·H_t, r·H_u)` is a same-scale pair on the `t`-ray.  So the two-multiplier
form is the WHOLE lattice.

**2. The cone annihilator umbrella.**  One certified kill anywhere on the
cone — `(h, N) = (m·H_t, q·H_t)` at arbitrarily large `t` — contradicts
flatness and proves #249
(`irrational_totient_series_of_lcm_cone_certificate_supply`).  The wave-23
diagonal is the cell `q = m = 1`; q-ray steps are `m = 1`; q-gaps are free
`m`; prime-jump pairs `H_{t+1} - H_t` are `(q, m) = (1, p-1)`.  All the
advisory families are cells of this one theorem.

**3. Certificate completeness.**  The endpoint certificate is COMPLETE, not
just sound: some depth `L` certifies `(h, N)` IFF the tail difference
`R_{N+h} - R_N` is a non-integer
(`exists_certifiedKill_iff_tail_diff_notMem_int`).  Non-integrality is the
mathematical object; certificates are its finite receipts.  The frontier of
#249 in pure form: the diagonal (or any cone) tail differences are
non-integral at arbitrarily large scales
(`irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`,
`…_of_lcm_cone_nonintegrality_supply`).

**4. Rank-2 second differences — sound, and measured NOT shallower.**
`certifiedRank2Kill` certifies `(R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N) ∉ ℤ`
with a doubled band radius (`second_diff_notMem_int_of_certifiedRank2Kill`);
on q-rays rationality forces both first differences integral, so rank-2 kills
also prove #249 (`irrational_totient_series_of_lcm_qray_rank2_supply`).  The
wave-24 probe measured the advisory-1 hope that cancelling the `H·C` shadow
makes kills easier: the cancellation is real (median `|D₂|/(H·C)` ≈ 0.15)
but rank-1 certifies at least as shallow in 30 of 40 cells (median depth
delta +1) — the certificate band scales with the position, not the shadow.
The verdict is kernel-checked at a fixture cell
(`rank2_kill_sound_but_not_shallower_at_cell`).

The supply hypotheses (`∀ t₀, ∃ t ≥ t₀, …`) remain the open content of #249
and are NOT claimed.  Everything here is elementary: lcm divisibility, the
tail-period law, geometric tails, and integer window arithmetic.
-/

set_option maxRecDepth 10000

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-! ## The scale ladder is a divisibility chain -/



/-! ## The cone flatness law: rationality flattens the whole lcm cone -/



/-! ## The cone annihilator umbrella -/



/-! ## Certificate completeness: kills exist exactly at non-integers -/











/-! ## The exact irrationality normal form -/















/-! ## The frontier in pure form: non-integrality supply -/





/-! ## Rank-2: the second-difference certificate -/

/-- Second-difference window discrepancy
`A₂ = A(h, N+h, L) - A(h, N, L)`: the depth-`L` truncation of
`2^L·((R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N))`. -/
def windowDiscrepancy2 (h N L : ℕ) : ℤ :=
  windowDiscrepancy h (N + h) L - windowDiscrepancy h N L

/-- The decidable rank-2 certificate: the residue of `A₂` modulo `2^L` avoids
the radius-`2(N+2h+L+2)` neighbourhood of `0`.  The doubled radius pays for
two window truncations; in exchange the second difference cancels the whole
`H·C` clean shadow on the lcm cone. -/
def certifiedRank2Kill (h N L : ℕ) : Prop :=
  (2 * ((N : ℤ) + 2 * h + L + 2)) < windowDiscrepancy2 h N L % 2 ^ L ∧
    windowDiscrepancy2 h N L % 2 ^ L < 2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)

instance (h N L : ℕ) : Decidable (certifiedRank2Kill h N L) :=
  inferInstanceAs (Decidable (_ ∧ _))





/-! ## Kernel-decided deposits: the measured verdicts, machine-checked -/











end TotientTailPeriodKiller
end Erdos249257


