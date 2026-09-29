-- Prove2me | Definitions.Def_Erdos249257_LcmConeNonflat
-- name    : Erdos249257_LcmConeNonflat
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:54:39.329904+00:00
-- url     : https://prove2.me/theorems/8d374b2d-b849-4aa0-814f-7cc00a478722
-- title:
--   Totient-window numerator and cone nonflatness certificate
-- statement:
--   This bundle defines a totient-weighted window numerator and a decidable list-based cone nonflatness certificate: each listed index must have another listed index whose window-numerator difference has a sufficiently large residue modulo 2^L.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/LcmConeNonflat.lean#L1-L540
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
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
# Wave 25: the cone non-flatness refuter — killing the menu, not the pair

Wave 24 proved that rationality forces ONE fractional constant on the whole
lcm cone `{k·H_t : k ≥ 1}`.  Every certificate so far interrogates that
constant through a single PAIR of cone points.  This file interrogates a
whole finite MENU `Q = [q₁, …, q_k]` of cone vertices at once.

**The refuter.**  At depth `L` each vertex `q·H` pins the real point
`2^L·R_{q·H}` inside the one-sided arc

  `[P_L(q·H), P_L(q·H) + (q·H + L + 2)]  (mod 2^L)`,

where `P_L` is the integer window numerator (`windowNumerator`) and the
radius is the one-sided deep-tail bound.  If ALL the vertices share one
fractional part — cone flatness — those arcs must share a common point.
`coneNonflatCert` is the decidable statement that every arc's LEFT ENDPOINT
escapes some arc of the menu; by an argmin argument this refutes ANY common
point, hence refutes joint flatness outright
(`exists_nonintegral_pair_of_coneNonflatCert`): some pair of menu vertices
has a non-integral tail difference.  No circle topology, no Helly: if a
common point existed, the vertex of MINIMAL deep tail would be a common
left endpoint, and the certificate row at that vertex is exactly its
denial.

**Why this is sharper than pairwise kills.**  `certifiedKill` charges the
two-sided band `±(N+h+L+2)` — the TOP vertex's radius on BOTH sides.  The
menu refuter charges each arc only its OWN one-sided radius, so its
information floor `2^L > max_q(q·H+L+2)` is HALF the pairwise floor, and
even a 2-menu can fire strictly below every pairwise kill of the same menu.
For `|Q| ≥ 3` the refutation is genuinely joint: the menu can be
inconsistent while every pair alone stays consistent (empty common
intersection without any empty pairwise intersection).  Probe v3 measures
the strict-win census; the kernel-checked fixtures below deposit the first
firing cells.

**Supply.**  One firing menu (positive vertices, one-sided floors) at
arbitrarily large scale proves #249
(`irrational_totient_series_of_lcm_cone_nonflat_supply`).  The lcm-jump
lane is also named once and for all: certified kills at
`(h, N) = (H_{t+1} - H_t, H_t)` at arbitrarily large `t` prove #249
(`irrational_totient_series_of_lcm_jump_kill_supply`) — jumps are the cone
cells `(q, m) = (1, p-1)` and need no side condition at all, because a
`h = 0` window can never be certified.

The supply hypotheses remain the open content of #249 and are NOT claimed.
Everything is elementary: geometric tails, an argmin over a finite menu,
and integer window arithmetic.
-/

set_option maxRecDepth 100000

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-! ## Small-prime support of the cone window argument (wave 30)

For every prime `p ≤ t`, `p ∣ periodLcm t`, so `q·periodLcm t + s ≡ s (mod p)`:
the primes `≤ t` dividing the cone window argument `q·H_t + s` are exactly the
primes dividing the offset `s`.  This is the elementary door behind the wave-29
rough identity `φ(qH_t+s) ≈ qH_t·φ(s)/s` and the wave-30 smooth-envelope split
`P_L = E_L − Δ_L` — below `2t` the window totients carry only `s`'s small-prime
structure plus a non-negative fresh-prime (`> t`) defect.  It is NOT a supply
step: it does not fire any certificate, it fixes the arithmetic of the window
argument. -/


/-! ## The window numerator and its one-sided tail band -/

/-- The depth-`L` window numerator `P_L(M) = Σ_{j<L} φ(M+1+j)·2^{L-1-j}`:
the integer layer of `2^L·R_M`, exact up to the one-sided deep tail
`0 ≤ 2^L·R_M - P_L(M) ≤ M+L+2`. -/
def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)



/-! ## The menu refuter -/

/-- **The cone non-flatness certificate.**  For the vertex menu `Q` at scale
`H` and depth `L`: every left endpoint `P_L(qᵢ·H)` escapes some arc
`[P_L(qⱼ·H), P_L(qⱼ·H) + (qⱼ·H+L+2)]` modulo `2^L`.  A `|Q|²` one-sided
window check; decidable. -/
def coneNonflatCert (H L : ℕ) (Q : List ℕ) : Prop :=
  ∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((windowNumerator (qi * H) L : ℤ) - (windowNumerator (qj * H) L : ℤ)) % 2 ^ L

instance (H L : ℕ) (Q : List ℕ) : Decidable (coneNonflatCert H L Q) :=
  inferInstanceAs (Decidable (∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((windowNumerator (qi * H) L : ℤ) - (windowNumerator (qj * H) L : ℤ)) % 2 ^ L))



/-! ## Supply: one firing menu at arbitrarily large scale proves #249 -/



/-! ## The lcm-jump lane, named once and for all -/



/-! ## Exactness and depth-monotonicity of the menu refuter

Wave 27.  The probe's argmin characterisation — certificate fires iff NO
common point exists — and the depth law behind `nonflat_L_min` become
kernel facts.  Three moving parts, all elementary: a purely combinatorial
argmin (no analytic tails), the window recursion
`P_{L+1}(M) = 2·P_L(M) + φ(M+L+1)`, and a halving descent for common
points.  Consequences: the certificate is monotone in depth (fires at `L`
⟹ fires at every `L' ≥ L` with floors held), so `∃L` in any supply
statement collapses onto canonical large-enough depths, and the probe's
`nonflat_L_min` acquires kernel meaning as THE firing threshold. -/





















/-! ## Menu monotonicity: firing propagates to every supermenu, same depth

The other half of the refuter's order structure, and the sharper one.
Common points only SHRINK when arcs are added: a common point of the
larger menu `Q'` restricts (same witness, fewer constraints) to a common
point of any sub-menu `Q ⊆ Q'`.  So an EMPTY sub-menu intersection stays
empty under supersets — with no depth change and no floor condition.  This
is the exact reason the wave-25 joint wins exist (a menu can fire while
every sub-menu is silent: firing runs UPWARD in the menu, not down), and it
collapses the six-arc supply obligation onto the smallest prefix that
already fires. -/







/-! ## Kernel-decided deposits: the measured verdicts, machine-checked -/







end TotientTailPeriodKiller
end Erdos249257


