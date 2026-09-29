-- Prove2me | Definitions.Def_Erdos249257_CarrySurvivorExtinction
-- name    : Erdos249257_CarrySurvivorExtinction
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:44:42.791111+00:00
-- url     : https://prove2.me/theorems/6b8b26c0-491c-49b6-a4d1-1891f23414de
-- title:
--   Carry-orbit survivors and finite extinction certificate
-- statement:
--   This bundle defines a totient increment, a bounded congruence predicate for candidate endpoint survivors, a recurrence for their carry orbits, and a finite survivor-kill certificate; it also supplies decidability instances for the predicates.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/CarrySurvivorExtinction.lean#L1-L596
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
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
# Wave 22: carry-survivor extinction and the multiple-period collapse

Wave 21 reduced #249 to a certified kill supply: for every period `h ≥ 1` and
every threshold `N₀`, some `(N ≥ N₀, L)` with the endpoint residue certificate
`certifiedKill h N L`.  This file spends two further consequences of
rationality that the wave-21 socket left on the table.

**1. The multiple-period collapse.**  If `h₀` is an eventual binary period,
every multiple `m·h₀` is too, by pure telescoping:

  `D_{m·h}(N) = ∑_{i<m} D_h(N + i·h)`,   `D_h(N) = R_{N+h} - R_N`.

So the supply obligation weakens from *kill every `h`* to *kill one multiple
per divisibility ray* (`irrational_totient_series_of_multiple_survivor_supply`)
— and further collapses onto the ONE-PARAMETER family `lcm(1..t)`, since every
`h₀ ≤ t` divides `lcm(1..t)`
(`irrational_totient_series_of_lcm_survivor_supply`).  The throat of #249
narrows from a ∀h family of targets to a single ℕ-indexed ray.

**2. The carry-survivor certificate.**  The wave-21 note called the
bounded-orbit reformulation advisory.  Here it is machine-checked: doubling
the tail shifts the window by one and expels the head totient
(`totientTail_succ`), so an integer tail difference `d = D_h(N)` launches the
exact integer orbit

  `orbit 0 = d`,  `orbit (i+1) = 2·orbit i - (φ(N+i+1+h) - φ(N+i+1))`,

which tracks `D_h(N+i)` forever (`carryOrbit_eq_tail_diff`) and is therefore
trapped in the strip `|·| < N+i+h+2` (`abs_tail_diff_lt`).  The certificate
`survivorKill h N K` checks — finitely, decidably — that every integer
candidate in the initial box escapes the strip within `K` steps; soundness is
`tail_diff_notMem_int_of_survivorKill`.  The survivor predicate is strictly
stronger than the endpoint certificate at equal depth
(`survivor_strict_at_equal_budget`, a `decide` witness at `(1, 57, 8)`), but
the wave-22 probe measures the two families as near-equivalent in minimal
kill depth — the deepest scale dominates.  The probe's honest summary: the
multiple-period loosening is the logical gain; the survivor form is the
bounded-orbit lane made kernel-checkable.

**Deposits.**  `certifiedKill_all_upto_sixteen` machine-checks kills for every
`h ≤ 16` at `(N, L) = (14, 9)` — twice the wave-21 period range in a smaller
window — giving the extended exclusion
`totient_series_ne_rat_of_den_dvd_upto_sixteen`: `S` is no rational whose
denominator divides `2¹⁴·(2ʰ-1)` for any `h ≤ 16`.

Everything remains elementary: `φ(n) ≤ n`, geometric tails, integer orbit
arithmetic.  No q-Padé, no Stern–Brocot, no unformalised citations.
-/

set_option maxRecDepth 10000

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-! ## Tail bounds: the strip that traps every integer carry orbit -/







/-! ## The carry recurrence -/





/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. -/
def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)











/-- The signed endpoint-survivor fibre at depth `L`.  Its elements are the
integer representatives of the exact discrepancy residue that still fit in
the analytic endpoint corridor. -/
def endpointSurvivor (h N L : ℕ) (z : ℤ) : Prop :=
  |z| ≤ (N + h + L + 2 : ℤ) ∧
    z % 2 ^ L = windowDiscrepancy h N L % 2 ^ L

instance (h N L : ℕ) (z : ℤ) : Decidable (endpointSurvivor h N L z) :=
  inferInstanceAs (Decidable (_ ∧ _))











/-! ## The integer carry orbit and the survivor certificate -/

/-- The integer carry orbit launched from candidate `d` at position `N`:
`orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`.  If `D_h(N)` is the
integer `d`, this orbit equals `D_h(N+i)` forever. -/
def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)



/-- The **carry-survivor certificate**: every integer candidate in the initial
box `|d| ≤ N+h+1` — enumerated as `d = j - (N+h+1)` for `j < 2·(N+h+1)+1` —
provably escapes the strip `|·| ≤ N+i+h+1` within `K` steps (escape stated as
a two-sided disjunction).  Finitely many candidates, finitely many steps:
decidable. -/
def survivorKill (h N K : ℕ) : Prop :=
  ∀ j ∈ Finset.range (2 * (N + h + 1) + 1),
    ∃ i ∈ Finset.range (K + 1),
      carryOrbit h N ((j : ℤ) - (N + h + 1)) i ≤ -(N + i + h + 2 : ℤ)
        ∨ (N + i + h + 2 : ℤ) ≤ carryOrbit h N ((j : ℤ) - (N + h + 1)) i

instance (h N K : ℕ) : Decidable (survivorKill h N K) := by
  unfold survivorKill
  infer_instance



/-! ## The multiple-period collapse -/









/-! ## The one-parameter collapse: `lcm(1..t)` is a universal period ray -/









/-! ## Unconditional deposits (kernel-decided) -/














end TotientTailPeriodKiller
end Erdos249257


