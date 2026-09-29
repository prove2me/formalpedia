-- Prove2me | Definitions.Def_Combinatorics_MagnitudeMirrorSeal
-- name    : Combinatorics_MagnitudeMirrorSeal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:44:37.729417+00:00
-- url     : https://prove2.me/theorems/111d7ff8-5683-4bd2-ac1a-bce7310b4b2b
-- title:
--   Aether Catalog definitions — Combinatorics_MagnitudeMirrorSeal
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.MagnitudeMirrorSeal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/MagnitudeMirrorSeal.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_Round11FingerprintInformation
/-
# Round-70 #6 — the magnitude-mirror seal: energy-ascent sensors are structural,
# spectral summaries are mirrors of `N`, and only the positional oracle survives

Formal companion to the round-70 correction round (exps 549 + 551), which
*retracted* the "energy-ascent channel" of papers 193/195 and re-sealed the
Pythagorean/Fermat tree against every realized probe class.

The experimental report contains three separate claims.  This file turns each of
them into an exact, finitary theorem, using the catalog's counting notion of
independence `Round11.ZeroInfo` (`Combinatorics.Round11FingerprintInformation`)
as the common currency — `ZeroInfo Ω T S` says that every joint fibre of the
statistic `T` and the secret `S` on the instance set `Ω` has exactly the product
cardinality, i.e. the empirical mutual information is *exactly* `0`, not merely
small.

* **The energy-ascent artifact (exp549).**  With `E(a) = a² − N` and the
  isqrt-anchored window `a_j = ⌊√N⌋ + j`, the sign of `E` on the window is
  completely determined *before* any arithmetic of `N` enters:
  `energy_anchor_nonpos` and `energy_pos_of_index_pos` show `E(a₀) ≤ 0 < E(a_j)`
  for every `j ≥ 1`.  So the zero crossing sits between `j = 0` and `j = 1`
  (at `√N`) for **every** `N`, never at `j = d`
  (`no_sign_change_at_positive_offset`).  Consequently the whole sign vector of
  the window is a *constant* function of `N` on any family of non-squares
  (`signVector_const`), and therefore carries exactly zero information about any
  secret whatsoever (`bracket_sensor_zeroInfo`), as does any post-processing of
  it (`bracket_sensor_zeroInfo_postprocessed`).  This is the formal content of
  the measured `MI(hits;b₁) = 0.000000`.
* **The Fermat square-hit is the real event.**  `fermat_hit_of_factorization`
  and `fermat_hit_factorization` show the *hit* `E(a) = b²` — not the sign
  change — is equivalent to a factorization `N = (a−b)(a+b)`, and
  `hit_at_anchor_iff_isSquare` shows the anchor itself is a hit precisely for
  perfect squares.
* **The magnitude mirror (exp551).**  A feature that is a deterministic function
  of `N`'s magnitude inherits *all* of its information from the magnitude
  (`zeroInfo_of_mirror`), is *exactly* as informative as the magnitude when the
  reparametrisation is injective — in particular strictly monotone, e.g. `log N`
  versus any increasing rescaling of it (`zeroInfo_congr_of_injective`,
  `zeroInfo_congr_of_strictMono`) — and collapses to *exactly* zero information
  inside every magnitude cell (`mirror_conditional_zeroInfo`).
* **The method lesson, as a theorem.**  `stratification_is_not_transfer`
  exhibits an explicit instance set on which a magnitude mirror has *nonzero*
  unconditional information yet *exactly zero* information inside every
  magnitude cell: marginal signal from a deterministic function of `N` is scale
  stratification, not transfer.  This is why a row-shuffle permutation null is
  the wrong null.
* **What survives: the positional oracle.**  For the factor-derived oracle bit
  `1{d ≤ B}` the empirical below-threshold fraction is monotone in `B`
  (`belowFrac_monotone`), its capacity is at most one bit
  (`oracle_capacity_le_log_two`, and the counting form
  `oracle_bit_pigeonhole`), it ascends below the median and descends above it
  (`oracle_capacity_ascending`, `oracle_capacity_descending`), and the peak is
  attained exactly at balance (`oracle_capacity_eq_log_two_iff`) — the formal
  shape of the measured profile "peak `0.4798` at `B ≈ 22758`".  Crucially the
  oracle bit is **not** a magnitude mirror (`positional_oracle_not_mirror`), so
  it is not killed by the exp551 argument, and it is genuinely informative
  (`positional_oracle_informative`).
-/

namespace MagnitudeMirror

open Finset Round11

/-! ## 1. The energy function of the isqrt-anchored window -/

/-- The Fermat energy `E(a) = a² − N`. -/
def energy (N a : ℕ) : ℤ := (a : ℤ) ^ 2 - (N : ℤ)

/-- The anchor of the window: `⌊√N⌋`. -/
def anchor (N : ℕ) : ℕ := Nat.sqrt N

/-- The `j`-th point of the isqrt-anchored window. -/
def windowPoint (N j : ℕ) : ℕ := anchor N + j







/-! ## 2. The Fermat square-hit is the real event -/






/-! ## 3. Bracket / sign-count sensors are structural: exact zero information -/

/-- The bracket sensor read off a length-`L` isqrt-anchored window: the vector of
signs of the energy. -/
def signVector (L N : ℕ) : Fin L → ℤ :=
  fun j => (energy N (windowPoint N (j : ℕ))).sign

/-- The number of window indices at which the energy is negative. -/
def negCount (L N : ℕ) : ℕ :=
  #{j ∈ Finset.range L | energy N (windowPoint N j) < 0}



variable {α : Type*} {β γ δ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq δ]




/-! ## 4. General information calculus for `ZeroInfo` -/




/-- `Φ` *mirrors the magnitude* `M` on `Ω` when it is a deterministic function of
`M` there. -/
def MirrorsMagnitude {μ : Type*} (Ω : Finset α) (Φ : α → β) (M : α → μ) : Prop :=
  ∃ g : μ → β, ∀ w ∈ Ω, Φ w = g (M w)




/-! ## 5. The method lesson: stratification is not transfer -/


/-! ## 6. What survives: the factor-derived positional oracle -/

/-- The empirical fraction of instances whose smallest factor is at most `B`. -/
noncomputable def belowFrac (Ω : Finset α) (d : α → ℕ) (B : ℕ) : ℝ :=
  (#(Ω.filter fun w => d w ≤ B) : ℝ) / (#Ω : ℝ)











end MagnitudeMirror


