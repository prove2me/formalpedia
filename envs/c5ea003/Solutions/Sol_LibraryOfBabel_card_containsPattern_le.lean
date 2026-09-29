-- Prove2me | solution 1 for LibraryOfBabel.card_containsPattern_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:13:21.964794+00:00
-- url     : https://prove2.me/submissions/c4fd96a5-bbd7-4666-aa24-c30eed8adbf9

-- Sol generated from Cryptography/LibraryOfBabel/Probability.lean
import Mathlib
import Definitions.Def_Cryptography_LibraryOfBabel_Basic
import Definitions.Def_Cryptography_LibraryOfBabel_Probability
import Theorems.Thm_LibraryOfBabel_card_occursAt
/-
# The Library of Babel: Probability of Finding Meaning

Borges asks: what is the chance that a random volume contains a given passage —
a proof, a theorem, a sentence?  Here `p : Fin m → Fin A` is the target passage
(length `m`), and a volume *contains* it if the passage appears as a contiguous
window somewhere inside the book.

## Main Results (this file)

1. **Occurrence union bound** (`card_containsPattern_le`): the number of volumes
   containing a fixed length-`m` passage anywhere is at most
   `(L - m + 1) · A ^ (L - m)` — one term `A^(L-m)` per starting position, summed
   over the `L - m + 1` possible windows.

2. **Probability bound** (`prob_containsPattern_le`): dividing by the Library
   size `A ^ L`, the probability that a uniformly random volume contains the
   passage is at most `(L - m + 1) · A ^ (-m)`.  This is the rigorous form of the
   theme's heuristic `|T| · 25^{-k}`: the "meaning density" of the Library decays
   like the alphabet size raised to the *minus* passage length.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the theme claims the probability of a random volume
containing a proof of `T` is `≈ |T| · 25^{-k}`.  Read literally this is a union
bound: `#windows · Pr[match at a fixed window]`.

Experiment (Experimenter): a fixed window of length `m` is matched by exactly a
`A^{-m}` fraction of volumes (Basic.card_occursAt).  There are `L - m + 1`
windows, so a union bound gives `(L-m+1)·A^{-m}`.  Sanity check `A=2, L=3, m=2`:
`(3-2+1)·2^{-2} = 2·(1/4) = 1/2`.  Direct enumeration of the 8 binary strings of
length 3 shows exactly those containing "11" or "00" as a window — 6 of them, so
the true probability `6/8 = 3/4`.  The bound `1/2` is *not* an upper bound here?
Recheck: pattern is a *single fixed* `p`, not "any repeat".  For `p = (1,1)` the
strings of length 3 containing `11` are `110,011,111` → 3, and `3/8 ≤ 1/2 ✓`.

Analysis (Analyst): the inclusion–exclusion overcount (windows can overlap) means
the union bound is genuine (`≤`, not `=`).  The clean proof route is
`filter Contains = ⋃_i filter (OccursAt window_i)` then `card_biUnion_le` and the
exact per-window count from `Basic.card_occursAt`.

Critique (Critic): the heuristic's leading factor is `|T| = m`, but the honest
combinatorial factor is the number of *windows* `L - m + 1`, which for `m ≪ L`
is `≈ L`, not `m`.  So the theme's `|T|·25^{-k}` mis-identifies the polynomial
prefactor; the correct statement replaces `|T|` by the number of placements
`L - |T| + 1`.  We prove the corrected inequality.
-/

open Finset Fintype Function LibraryOfBabel

open LibraryOfBabel


/-- Each window is an injective family of positions. -/
theorem window_injective {L m : ℕ} (hm : m ≤ L) (i : Fin (L - m + 1)) :
    Function.Injective (window hm i) := by
  intro a b hab
  simp only [window, Fin.mk.injEq] at hab
  exact Fin.ext (by omega)





open LibraryOfBabel in
theorem solution{A L m : ℕ} (hm : m ≤ L) (p : Fin m → Fin A) :
    Nat.card {s : Volume A L // ContainsPattern hm p s} ≤ (L - m + 1) * A ^ (L - m) := by
  classical
  -- Bridge `Nat.card` of the subtype to a `Finset.filter` cardinality.
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- The containing volumes are the union, over windows, of the per-window matches.
  have hsub :
      (univ.filter (fun s : Volume A L => ContainsPattern hm p s))
        ⊆ (univ : Finset (Fin (L - m + 1))).biUnion
            (fun i => univ.filter (fun s : Volume A L => OccursAt (window hm i) p s)) := by
    intro s hs
    simp only [mem_filter, mem_biUnion, mem_univ, true_and] at hs ⊢
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, hi⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  -- Each per-window match set has exactly `A^(L-m)` elements.
  have hcard : ∀ i : Fin (L - m + 1),
      (univ.filter (fun s : Volume A L => OccursAt (window hm i) p s)).card = A ^ (L - m) := by
    intro i
    have := card_occursAt (window hm i) (window_injective hm i) p
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  rw [Finset.sum_congr rfl (fun i _ => hcard i)]
  simp [mul_comm]
