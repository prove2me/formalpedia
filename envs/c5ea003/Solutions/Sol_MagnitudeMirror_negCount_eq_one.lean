-- Prove2me | solution 1 for MagnitudeMirror.negCount_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:59:46.070523+00:00
-- url     : https://prove2.me/submissions/2cb11b0d-e508-484e-ad24-7c7f78c44bae

-- Sol generated from Combinatorics/MagnitudeMirrorSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_MagnitudeMirrorSeal
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

open MagnitudeMirror

open Finset Round11

/-! ## 1. The energy function of the isqrt-anchored window -/




@[simp] theorem windowPoint_zero (N : ℕ) : windowPoint N 0 = anchor N := by
  simp [windowPoint]

/-- `E(a) = 0` exactly at the square root: the energy zero is at `√N`. -/
theorem energy_eq_zero_iff (N a : ℕ) : energy N a = 0 ↔ a * a = N := by
  constructor
  · intro h
    have : (a : ℤ) * a = (N : ℤ) := by
      have := h; simp only [energy, sub_eq_zero] at this; nlinarith [this]
    exact_mod_cast this
  · intro h
    simp only [energy, sub_eq_zero, ← h]
    push_cast
    ring

/-- At the anchor the energy is never positive. -/
theorem energy_anchor_nonpos (N : ℕ) : energy N (anchor N) ≤ 0 := by
  have h : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have : ((Nat.sqrt N : ℤ)) * (Nat.sqrt N : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
  simp only [energy, anchor, sub_nonpos]
  nlinarith [this]

/-- At every strictly positive offset the energy is strictly positive: the sign
change of `E` on an isqrt-anchored window always happens between `j = 0` and
`j = 1`. -/
theorem energy_pos_of_index_pos (N j : ℕ) (hj : 1 ≤ j) :
    0 < energy N (windowPoint N j) := by
  have h : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have hZ : (N : ℤ) < ((Nat.sqrt N : ℤ) + 1) * ((Nat.sqrt N : ℤ) + 1) := by
    exact_mod_cast h
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hm : (0 : ℤ) ≤ (Nat.sqrt N : ℤ) := Int.natCast_nonneg _
  simp only [energy, windowPoint, anchor, sub_pos]
  push_cast
  nlinarith [hZ, hj', hm]



/-! ## 2. The Fermat square-hit is the real event -/




/-- The anchor is a Fermat hit with `b = 0` exactly for perfect squares — the
only way the "event at `a = m`" can occur. -/
theorem hit_at_anchor_iff_isSquare (N : ℕ) :
    energy N (anchor N) = 0 ↔ IsSquare N := by
  rw [energy_eq_zero_iff]
  constructor
  · intro h; exact ⟨Nat.sqrt N, h.symm⟩
  · rintro ⟨k, hk⟩
    subst hk
    simp [anchor, Nat.sqrt_eq]

/-- For a non-square `N` the anchor energy is strictly negative. -/
theorem energy_anchor_neg_of_not_isSquare {N : ℕ} (h : ¬ IsSquare N) :
    energy N (anchor N) < 0 :=
  lt_of_le_of_ne (energy_anchor_nonpos N) (fun hc => h ((hit_at_anchor_iff_isSquare N).1 hc))

/-! ## 3. Bracket / sign-count sensors are structural: exact zero information -/





variable {α : Type*} {β γ δ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq δ]




/-! ## 4. General information calculus for `ZeroInfo` -/








/-! ## 5. The method lesson: stratification is not transfer -/


/-! ## 6. What survives: the factor-derived positional oracle -/













open MagnitudeMirror in
theorem solution{L N : ℕ} (hL : 1 ≤ L) (h : ¬ IsSquare N) : negCount L N = 1 := by
  classical
  have hfil : {j ∈ Finset.range L | energy N (windowPoint N j) < 0} = {0} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hneg⟩
      by_contra hj
      exact absurd hneg (not_lt.2 (le_of_lt (energy_pos_of_index_pos N j (by omega))))
    · rintro rfl
      exact ⟨by omega, by simpa using energy_anchor_neg_of_not_isSquare h⟩
  simp [negCount, hfil]
