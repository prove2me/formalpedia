-- Prove2me | solution 1 for MagnitudeMirror.stratification_is_not_transfer
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:02:25.399525+00:00
-- url     : https://prove2.me/submissions/7c96097e-2c70-4476-9fc7-08b4d0bea5a8

-- Sol generated from Combinatorics/MagnitudeMirrorSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_MagnitudeMirrorSeal
import Definitions.Def_Combinatorics_Round11FingerprintInformation
import Theorems.Thm_Round11_not_zeroInfo_pair
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










/-! ## 2. The Fermat square-hit is the real event -/






/-! ## 3. Bracket / sign-count sensors are structural: exact zero information -/





variable {α : Type*} {β γ δ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq δ]




/-! ## 4. General information calculus for `ZeroInfo` -/







/-- Every statistic is uninformative on a one-point instance set. -/
theorem zeroInfo_singleton {T : α → β} {S : α → γ} (w : α) :
    ZeroInfo ({w} : Finset α) T S := by
  classical
  intro t s
  by_cases ht : T w = t <;> by_cases hs : S w = s <;>
    simp [Finset.filter_singleton, ht, hs]

/-! ## 5. The method lesson: stratification is not transfer -/


/-! ## 6. What survives: the factor-derived positional oracle -/













open MagnitudeMirror in
theorem solution:
    ∃ (Ω : Finset ℕ) (M : ℕ → ℕ) (Φ : ℕ → ℕ) (S : ℕ → ℕ),
      StrictMono (fun n : ℕ => 2 * n) ∧
      (∀ w, Φ w = 2 * M w) ∧
      MirrorsMagnitude Ω Φ M ∧
      ¬ ZeroInfo Ω Φ S ∧
      ∀ c : ℕ, ZeroInfo (Ω.filter fun w => M w = c) Φ S := by
  classical
  refine ⟨{2, 3}, id, fun n => 2 * n, fun n => n % 2,
    ?_, fun w => rfl, ⟨fun m => 2 * m, fun w _ => rfl⟩, ?_, ?_⟩
  · intro a b hab
    dsimp only
    omega
  · exact not_zeroInfo_pair (by decide) (by decide) (by decide)
  · intro c
    have hsub : ({2, 3} : Finset ℕ).filter (fun w => id w = c) ⊆ {c} := by
      intro w hw
      rw [Finset.mem_filter] at hw
      simpa using hw.2
    rcases Finset.subset_singleton_iff.1 hsub with h | h
    · rw [h]; intro t s; simp
    · rw [h]; exact zeroInfo_singleton c
