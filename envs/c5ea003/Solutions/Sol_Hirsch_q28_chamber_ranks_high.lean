-- Prove2me | solution 1 for Hirsch.q28_chamber_ranks_high
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T23:20:30.760589+00:00
-- url     : https://prove2.me/submissions/7e091c8d-03a5-4acf-b9cb-448f0103cbeb

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Classical Hirsch Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem checkChunk_11 : checkChunk 1100 100 = true := rfl
theorem checkChunk_12 : checkChunk 1200 100 = true := rfl
theorem checkChunk_13 : checkChunk 1300 100 = true := rfl
theorem checkChunk_14 : checkChunk 1400 100 = true := rfl
theorem checkChunk_15 : checkChunk 1500 100 = true := rfl
theorem checkChunk_16 : checkChunk 1600 100 = true := rfl
theorem checkChunk_17 : checkChunk 1700 100 = true := rfl
theorem checkChunk_18 : checkChunk 1800 100 = true := rfl
theorem checkChunk_19 : checkChunk 1900 100 = true := rfl
theorem checkChunk_20 : checkChunk 2000 2 = true := rfl

lemma checkChunk_spec (off n r : ℕ)
    (h : checkChunk off n = true) (h1 : off ≤ r) (h2 : r < off + n) :
    certOkUnrank r = true := by
  have hr : r - off < n := by omega
  have hall := (List.all_eq_true.mp h) (r - off) (List.mem_range.mpr hr)
  have : off + (r - off) = r := Nat.add_sub_of_le h1
  simpa [this] using hall


theorem solution :
    ∀ r : ℕ, 1100 ≤ r → r < 2002 → certOkUnrank r = true := by
  intro r hlo hr
  rcases Nat.lt_or_ge r 1200 with h | h
  · exact checkChunk_spec 1100 100 r checkChunk_11 hlo h
  rcases Nat.lt_or_ge r 1300 with h2 | h2
  · exact checkChunk_spec 1200 100 r checkChunk_12 h h2
  rcases Nat.lt_or_ge r 1400 with h3 | h3
  · exact checkChunk_spec 1300 100 r checkChunk_13 h2 h3
  rcases Nat.lt_or_ge r 1500 with h4 | h4
  · exact checkChunk_spec 1400 100 r checkChunk_14 h3 h4
  rcases Nat.lt_or_ge r 1600 with h5 | h5
  · exact checkChunk_spec 1500 100 r checkChunk_15 h4 h5
  rcases Nat.lt_or_ge r 1700 with h6 | h6
  · exact checkChunk_spec 1600 100 r checkChunk_16 h5 h6
  rcases Nat.lt_or_ge r 1800 with h7 | h7
  · exact checkChunk_spec 1700 100 r checkChunk_17 h6 h7
  rcases Nat.lt_or_ge r 1900 with h8 | h8
  · exact checkChunk_spec 1800 100 r checkChunk_18 h7 h8
  rcases Nat.lt_or_ge r 2000 with h9 | h9
  · exact checkChunk_spec 1900 100 r checkChunk_19 h8 h9
  · exact checkChunk_spec 2000 2 r checkChunk_20 h9 hr
