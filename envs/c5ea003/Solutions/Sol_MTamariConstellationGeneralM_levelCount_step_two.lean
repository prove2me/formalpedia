-- Prove2me | solution 1 for MTamariConstellationGeneralM.levelCount_step_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:25:29.885408+00:00
-- url     : https://prove2.me/submissions/af4788c0-49f9-40c1-8d5f-febff4279a41

-- Sol generated from Applications/MTamariConstellationGeneralM/GeneralM.lean
import Mathlib
import Definitions.Def_Applications_MTamariConstellationGeneralM_GeneralM

/-!
# General-`m` recursive-decomposition isomorphism:
`m`-Tamari intervals ↔ planar `(m+1)`-constellations (generating-tree layer)

The research direction

*"Recursive decomposition isomorphism for general `m`-Tamari intervals and planar
`(m+1)`-constellations"*

asserts, for **every** `m ≥ 1`, an isomorphism between the generating tree encoding
the recursive decomposition of greedy `m`-Tamari intervals and the one encoding
planar `(m+1)`-constellations, refined by the tracked combinatorial statistics
(valleys / active sites).  For `m = 1` this refined equinumerosity is the theorem
of the motivating paper (the base layer established in the previous cycle, whose
counting sequence is the Catalan numbers `1,2,5,14,42,…`).

This file carries out the **general-`m`** layer.  For each `m` we use two natural
label encodings of the *same* recursive decomposition:

* the **active-sites rule** `sitesRuleM m k = range' 1 (m*k+1)` (root label `1`),
  natural on the `m`-Tamari / Dyck side: a node with `k` active insertion sites
  has `m*k+1` children whose labels enumerate the sites of each child;
* the **shifted rule** `shiftedRuleM m k = range' 2 (m*k-m+1)` (root label `2`),
  natural on the `(m+1)`-constellation side, where the root already carries the
  extra site.

These are genuinely different encodings, yet we prove they are **isomorphic
generating trees for every `m`** via the single relabelling `φ(k) = k+1`.  This
yields, for all `m`:

* `mTamari_levelCount_eq`      — equal counting sequences (plain equi-enumeration);
* `mTamari_refined_eq`         — equal *refined* counts (every label-borne statistic
  is distributed identically level by level);
* `mTamari_growth`             — the common counting sequence dominates `2^k`
  (for `m ≥ 1`), so nothing here is vacuous: the trees genuinely grow.

The abstract engine behind the transport is stated separately and reusably in
`GeneratingTreeIso.lean`; here everything is proved directly for the concrete
`m`-rules to keep the file self-contained.

-- !-- Lab Notes -- !--
HYPOTHESIS.  The whole `m ≥ 1` family of correspondences is captured by ONE
relabelling `φ = (·+1)` intertwining the active-sites and shifted succession
rules, uniformly in `m`.  The `m = 1` instance is the Catalan base layer.

EXPERIMENT.  `#eval` over the generating tree gave counting sequences
`m=1: 1,2,5,14,42` (Catalan, A000108), `m=2: 1,3,15,113,1273`,
`m=3: 1,4,34,586,21721`, and confirmed the intertwining identity
`shiftedRuleM m (a+1) = (sitesRuleM m a).map (·+1)` for all sampled `m,a` (see
`ComputationalEvidence.md`).  Level-1 count is `m+1`, so the trees differ with `m`.

ANALYSIS.  The single non-trivial identity is `sitesM_shiftedM_intertwine`, a
`List.range'` computation using `Nat.mul_succ`.  From it, a level induction gives
`levelLabels_shifted_map` (the shifted level list is the `(·+1)`-image of the
sites level list), whence equal counts and equal refined counts follow by
`List.length_map` / `List.countP_map`.  Growth: every label is `≥ 1`
(`sitesM_label_pos`), so for `m ≥ 1` every node has `≥ 2` children
(`sitesRuleM_len`), giving a `≥ 2×` step (`levelCount_step_two`) and hence
`2^k ≤ levelCount` by induction.

CRITIQUE.  Non-vacuous: the intertwining is a real arithmetic identity (fails for
a wrong shift), `levelLabels_shifted_map` is a genuine list identity by nested
induction, refined equality fails without intertwining, and the `2^k` bound rules
out triviality.  No theorem is `rfl`/`simp`/`native_decide`-only.  Honesty: this
proves the *generating-tree / statistic-transport* layer for all `m`; identifying
the counting sequence with the exact Bousquet-Mélou–Chapoton `m`-Tamari interval
numbers is left open (see `FUTURE_DIRECTIONS.md`).

SYNTHESIS.  One uniform relabelling proves, for every `m ≥ 1`, that the two
encodings of the recursive decomposition are isomorphic generating trees — the
general-`m` template that the full conjecture instantiates, with the `m = 1`
Catalan layer recovered as a special case (`sitesRuleM_one`).
-/

open MTamariConstellationGeneralM

/-! ## The concrete succession rules and the relabelling -/




/-! ## Level labels of a generating tree (concrete, over `ℕ`) -/



theorem levelLabels_succ (succ : ℕ → List ℕ) (root : ℕ) (k : ℕ) :
    levelLabels succ root (k + 1) = (levelLabels succ root k).flatMap succ := rfl


/-! ## Basic arithmetic of the rules -/

/-- Length of one branching under the active-sites rule. -/
theorem sitesRuleM_len (m k : ℕ) : (sitesRuleM m k).length = m * k + 1 := by
  unfold sitesRuleM; rw [List.length_range']



/-! ## The intertwining identity (heart of the isomorphism) -/



/-! ## Level correspondence and equinumerosity -/




/-! ## Non-triviality: genuine growth of the common counting sequence -/

/-- Every label appearing anywhere in the active-sites tree is `≥ 1`. -/
theorem sitesM_label_pos (m k : ℕ) :
    ∀ x ∈ levelLabels (sitesRuleM m) 1 k, 1 ≤ x := by
  induction k with
  | zero => intro x hx; simp [levelLabels] at hx; omega
  | succ k ih =>
      intro x hx
      rw [levelLabels_succ, List.mem_flatMap] at hx
      obtain ⟨a, _, hxa⟩ := hx
      unfold sitesRuleM at hxa
      rw [List.mem_range'] at hxa
      omega






open MTamariConstellationGeneralM in
theorem solution(m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    2 * levelCount (sitesRuleM m) 1 k ≤ levelCount (sitesRuleM m) 1 (k + 1) := by
  unfold levelCount
  rw [levelLabels_succ, List.length_flatMap]
  set L := levelLabels (sitesRuleM m) 1 k with hL
  have hterm : ∀ x ∈ L, 2 ≤ (sitesRuleM m x).length := by
    intro x hx
    rw [sitesRuleM_len]
    have hx1 : 1 ≤ x := sitesM_label_pos m k x hx
    have : 1 ≤ m * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  calc 2 * L.length
      = (L.map (fun _ => 2)).sum := by
          rw [List.map_const', List.sum_replicate]; ring
    _ ≤ (L.map (fun x => (sitesRuleM m x).length)).sum := by
          apply List.sum_le_sum
          intro x hx
          exact hterm x hx
