-- Prove2me | Theorems.Thm_mme_more_asymmetry_canonical_112_joint_histogram
-- name    : mme_more_asymmetry_canonical_112_joint_histogram
-- status  : Open
-- author  : @WillR
-- created : 2026-09-27T19:46:10.161046+00:00
-- url     : https://prove2.me/theorems/b17d8d62-6e10-4c5d-8ce7-5474b2967903
-- title:
--   Exact four-row joint histogram for a canonical 112 child
-- statement:
--   For any nonnegative population parameter h and any canonical 112 profile parameter c/(2q), with c ≤ q, the four explicitly defined joint two-letter rows have exactly the prescribed mode-wise word histograms, every supported row has grade 2 at each position, and the total population is 2*h*q. This includes zero population and both profile endpoints. The joint table is retained explicitly so it can feed the child matrix extraction theorem.
-- source:
--   Exact finite combinatorial coupling for the canonical (1,1,2) child profile, matching the pinned `CompleteWord` and physical Stage conventions in Definitions.Def_mme_recursive_yz_physical_words. The 112 proportions are the exact profile family in Proved theorem mme_complete_split_112_parametric_profile_canonical_stars; this lemma supplies its explicit integer joint histogram at a common denominator. Mathlib revision 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e.

import Definitions.Def_mme_recursive_yz_physical_words
import Mathlib.Tactic

open BigOperators MME.CompleteSplit
set_option autoImplicit false

private abbrev CW2 := CompleteWord 2

private def word01 : CW2 := fun r => if r.val = 0 then 0 else 1
private def word10 : CW2 := fun r => if r.val = 0 then 1 else 0
private def word02 : CW2 := fun r => if r.val = 0 then 0 else 2
private def word20 : CW2 := fun r => if r.val = 0 then 2 else 0
private def word11 : CW2 := fun _ => 1

private def rowA : Fin 3 → CW2 := fun i =>
  if i.val = 0 then word01 else if i.val = 1 then word01 else word20
private def rowB : Fin 3 → CW2 := fun i =>
  if i.val = 0 then word01 else if i.val = 1 then word10 else word11
private def rowC : Fin 3 → CW2 := fun i =>
  if i.val = 0 then word10 else if i.val = 1 then word01 else word11
private def rowD : Fin 3 → CW2 := fun i =>
  if i.val = 0 then word10 else if i.val = 1 then word10 else word02

/-- Four joint rows, with the released `112` profile parameter `c/(2q)`.
The total marginal population is `2*q*h`; `q` is half the common denominator. -/
private def joint112 (q h c : ℕ) (v : Fin 3 → CW2) : ℕ :=
  if v = rowA then h * c
  else if v = rowB then h * (q - c)
  else if v = rowC then h * (q - c)
  else if v = rowD then h * c
  else 0

/-- The three prescribed complete-word histograms for the canonical `112` cell. -/
private def mu112 (q h c : ℕ) (i : Fin 3) (s : CW2) : ℕ :=
  if i.val = 2 then
    if s = word02 ∨ s = word20 then h * c
    else if s = word11 then h * (q - c) + h * (q - c)
    else 0
  else if s = word01 ∨ s = word10 then h * q
  else 0

theorem mme_more_asymmetry_canonical_112_joint_histogram (q h c : ℕ) (hc : c ≤ q) :
    (∀ i s, (∑ v : Fin 3 → CW2, if v i = s then joint112 q h c v else 0) =
      mu112 q h c i s) ∧
    (∀ v, 0 < joint112 q h c v →
      ∀ r : Fin 2,
        (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) ∧
    (∑ v : Fin 3 → CW2, joint112 q h c v = h * q + h * q) := by sorry
