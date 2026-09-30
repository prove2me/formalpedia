-- Prove2me | solution 1 for Hirsch.q28_chamber_ranks_0_1099
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T23:34:08.005262+00:00
-- url     : https://prove2.me/submissions/bdf9b2d8-7ccd-405f-8b26-646e6f09032f

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Classical Hirsch Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem certOk_01234 : certOkAt 0 1 2 3 4 = true := rfl
theorem checkChunk_00 : checkChunk 0 100 = true := rfl
theorem checkChunk_01 : checkChunk 100 100 = true := rfl
theorem checkChunk_02 : checkChunk 200 100 = true := rfl
theorem checkChunk_03 : checkChunk 300 100 = true := rfl
theorem checkChunk_04 : checkChunk 400 100 = true := rfl
theorem checkChunk_05 : checkChunk 500 100 = true := rfl
theorem checkChunk_06 : checkChunk 600 100 = true := rfl
theorem checkChunk_07 : checkChunk 700 100 = true := rfl
theorem checkChunk_08 : checkChunk 800 100 = true := rfl
theorem checkChunk_09 : checkChunk 900 100 = true := rfl
theorem checkChunk_10 : checkChunk 1000 100 = true := rfl

lemma checkChunk_spec (off n r : ℕ)
    (h : checkChunk off n = true) (h1 : off ≤ r) (h2 : r < off + n) :
    certOkUnrank r = true := by
  have hr : r - off < n := by omega
  have hall := (List.all_eq_true.mp h) (r - off) (List.mem_range.mpr hr)
  have : off + (r - off) = r := Nat.add_sub_of_le h1
  simpa [this] using hall

theorem certOkUnrank_low (r : ℕ) (hr : r < 1100) : certOkUnrank r = true := by
  rcases Nat.lt_or_ge r 100 with h | h
  · exact checkChunk_spec 0 100 r checkChunk_00 (Nat.zero_le _) h
  rcases Nat.lt_or_ge r 200 with h2 | h2
  · exact checkChunk_spec 100 100 r checkChunk_01 h h2
  rcases Nat.lt_or_ge r 300 with h3 | h3
  · exact checkChunk_spec 200 100 r checkChunk_02 h2 h3
  rcases Nat.lt_or_ge r 400 with h4 | h4
  · exact checkChunk_spec 300 100 r checkChunk_03 h3 h4
  rcases Nat.lt_or_ge r 500 with h5 | h5
  · exact checkChunk_spec 400 100 r checkChunk_04 h4 h5
  rcases Nat.lt_or_ge r 600 with h6 | h6
  · exact checkChunk_spec 500 100 r checkChunk_05 h5 h6
  rcases Nat.lt_or_ge r 700 with h7 | h7
  · exact checkChunk_spec 600 100 r checkChunk_06 h6 h7
  rcases Nat.lt_or_ge r 800 with h8 | h8
  · exact checkChunk_spec 700 100 r checkChunk_07 h7 h8
  rcases Nat.lt_or_ge r 900 with h9 | h9
  · exact checkChunk_spec 800 100 r checkChunk_08 h8 h9
  rcases Nat.lt_or_ge r 1000 with h10 | h10
  · exact checkChunk_spec 900 100 r checkChunk_09 h9 h10
  · exact checkChunk_spec 1000 100 r checkChunk_10 h10 hr


theorem solution :
    ∀ r : ℕ, r < 1100 → certOkUnrank r = true :=
  certOkUnrank_low
