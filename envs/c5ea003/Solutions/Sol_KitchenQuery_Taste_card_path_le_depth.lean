-- Prove2me | solution 1 for KitchenQuery.Taste.card_path_le_depth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T08:09:38.826558+00:00
-- url     : https://prove2.me/submissions/b15d0727-adb9-4fbe-a6a0-652f6dd79de9

/-
# `KitchenQuery.Taste.card_path_le_depth`
Target `b16b10b5` (Open; re-read live immediately before submitting).

ORDINARY PROOF — `scripts/screen_bundles.sh` returns CLEAN (exit 0). Gift check with the corrected
logic: **SAFE** — no sketch has this as its last unproved premise.

BINDERS — this target has NO WA (its history is CE,CE,CE,CE,CE), so no rejection publishes an
expected type. But unlike `d91f67b6`, the risk here is low: the statement declares its arguments
INLINE — `(t : Taste n) (x : Pantry n)` — and the only section-inherited binder is
`variable {n : ℕ}` inside `namespace Taste` (bundle line 63). The generated gate remains the
authority and fails closed on any mismatch.

A CE-only history says nothing about difficulty — only that five submitters' FILES never compiled.

MATHS. The bundle retains everything needed:

    inductive Taste n | serve : Bool → Taste n | probe : Fin n → Taste n → Taste n → Taste n
    depth | serve _    => 0 | probe _ l r => 1 + max l.depth r.depth
    path  | serve _, _ => ∅ | probe i l r, x => insert i (if x i then path r x else path l x)

Structural induction on the tasting tree:
  * `serve` — the path is empty and the depth is 0, so `0 ≤ 0`;
  * `probe i l r` — the path inserts `i` into the path of ONE branch, so its size grows by at most
    one, while the depth is one more than the MAXIMUM of the two branch depths. The inductive
    hypothesis bounds the chosen branch's path by that branch's depth, and that branch's depth is at
    most the max.

Only one branch is taken, which is why `max` (not a sum) is the right bound.

PROBED, NOT GUESSED:
  * `Finset.card_insert_le (a) (s) : (insert a s).card ≤ s.card + 1`
  * `le_max_left` / `le_max_right`
  * `max` is NOT linear, so `omega` cannot reason about it directly — the branch depth bound is
    introduced as a hypothesis first, after which `omega` treats `max l.depth r.depth` as an opaque
    atom and the arithmetic is linear in it.
-/
import Mathlib
import Definitions.Def_Novelty_KitchenQueryComplexity

set_option autoImplicit false
set_option maxHeartbeats 400000

open KitchenQuery


open KitchenQuery in
/-- **The target, verbatim.** -/
theorem solution {n : ℕ} (t : Taste n) (x : Pantry n) :
    (t.path x).card ≤ t.depth := by
  induction t with
  | serve b => simp [Taste.path, Taste.depth]
  | probe i l r ihl ihr =>
      simp only [Taste.path, Taste.depth]
      refine le_trans (Finset.card_insert_le _ _) ?_
      -- only ONE branch is taken, so the max — not the sum — bounds it
      by_cases hx : x i
      · simp only [hx, if_pos]
        have hmax : r.depth ≤ max l.depth r.depth := le_max_right _ _
        omega
      · simp only [hx, if_neg, Bool.false_eq_true, not_false_eq_true]
        have hmax : l.depth ≤ max l.depth r.depth := le_max_left _ _
        omega
