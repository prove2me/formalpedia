-- Prove2me | solution 1 for Catalog.NET68.net68_code_fit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:56:02.965217+00:00
-- url     : https://prove2.me/submissions/2c1a3df0-3282-4efa-aaa2-4f36aed04eb0

-- Sol generated from Applications/NET68DomainJumpBudgetLaw.lean
import Mathlib
import Definitions.Def_Applications_NET68DomainJumpBudgetLaw
import Definitions.Def_Applications_NET73KneeDecoupling
/-
# NET-68 — CODE-NEEDS-FEWER-KEYS: the domain-parameterised budget law

**Lab notes (round 21 of the limited-memory axis, paper 153).**  Domain jump from
prose (Gutenberg words) to Python source (10 CPython stdlib files); byte-identical
harness, exact gate, bar `= 0.98` of full accuracy, fine grid of step `4`, 24 windows,
per-corpus held-out splits, deterministic.

| ctx  | code `k*` | prose `k*` | code full acc | shift |
|------|-----------|------------|---------------|-------|
| 512  | **12**    | 16         | 0.6296        | −4    |
| 1024 | **16**    | 20         | 0.6520        | −4    |

Code retained-accuracy sweeps (fraction of full accuracy):

* @512  : `4 ↦ 0.930 ✗, 8 ↦ 0.969 ✗, 12 ↦ 0.981 ✓, 16 ↦ 0.987, 20 ↦ 0.988, 24 ↦ 0.989`
* @1024 : `8 ↦ 0.960 ✗, 12 ↦ 0.976 ✗, 16 ↦ 0.981 ✓, 20 ↦ 0.986, 24 ↦ 0.987`

Pre-registered horns: **P1** (knees transfer within one fine step) CONFIRMED,
**P2** (the shift is exactly one fine grid step at *both* contexts) CONFIRMED,
**P3** (the easier-to-predict domain needs at least as many keys) REFUTED.

## What this file proves

*§1 The knee as an adjoint.*  `kneeIdx` is the least grid index clearing the bar.
`kneeIdx_le_iff` is a genuine Galois connection between the accuracy curve and the
budget axis; `kneeIdx_eq_succ_of_bracket` is the *data-determination* lemma — the knee
depends on exactly two measured points (the last failing and the first passing one), so
no unmeasured grid index can ever enter a knee claim.

*§2 The measurement.*  `net68_code512_knee`, `net68_code1024_knee`: **every** monotone
accuracy curve agreeing with the NET-68 code sweep at the two bracketing points has
knee index `3` resp. `4`, i.e. budget `12` resp. `16` keys.  The measured tables
`code512`, `code1024` are exhibited and proved monotone, so the hypotheses are not
vacuous (`net68_code512_knee_concrete`, `net68_code1024_knee_concrete`).

*§3 The parameterised budget law.*  `BudgetLaw` = `base(domain) + increment · doublings`.
`BudgetLaw.ext_of_two_points` (two contexts identify a law), `shift_const_iff_inc_eq`
(**the structural content of P2**: a context-independent inter-domain shift is
*equivalent* to a shared increment — so the measured −4 at both contexts is exactly the
evidence that the increment is a function of scale alone), `crossover_of_inc_lt`
(unequal increments force a crossover, hence P2 could have failed), `eval_sup'`
(the mixed-workload envelope is again a law, with base the largest base — the
deployment rule), `mixed_workload_law`, `sizing_by_code_underprovisions`.

*§4 The fit and its predictions.*  `codeLaw = ⟨12, 4⟩`, `proseLaw = ⟨16, 4⟩`;
`codeLaw_unique`/`proseLaw_unique` (the two measured points pin the law), `net68_shift`,
`net68_increment_shared`, `net68_shift_is_one_fine_step`, and the falsifiable
extrapolation `net68_prediction_4096`.

*§5 Grid aliasing.*  `coarse_grid_hides_shift`: on a grid of step `8` the code and prose
knees are indistinguishable; `shift_visible_iff` gives the exact resolution threshold.
The fine grid is not cosmetic — it is what makes P2 falsifiable.

*§6 Accuracy ⟂ knee (P3, structurally).*  Using the NET-73 attention-profile calculus,
`accuracy_knee_decoupled` realises *every* pair (full accuracy, knee), whence
`no_accuracy_functional_law` and `easier_can_need_fewer_or_more_keys`: P3 is not merely
false on the data, it is unprovable from any accuracy information whatsoever.

*§7 Concentration bridge.*  `fewer_keys_forces_heavier_key` and
`code_shift_forces_concentration_gap`: a knee of `12` where prose needs `16` *certifies*
that some code key carries more than `τ/13` of the attention mass — the −4 shift is a
measurable statement about the shape of code attention, not about its difficulty.
-/

open Catalog.NET68

open Catalog.NET73

/-! ## 1. The knee of a sweep, as an adjoint -/



variable {acc : ℕ → ℚ} {bar : ℚ}









/-! ## 2. The NET-68 measurement -/













/-! ## 3. The parameterised budget law -/


open BudgetLaw













/-! ## 4. The NET-68 fit -/

open BudgetLaw

















/-! ## 5. Grid aliasing: why the fine grid is what makes P2 falsifiable -/






/-! ## 6. Accuracy level ⟂ knee position: P3 is unprovable, not merely false -/







/-! ## 7. Concentration bridge: what a smaller base certifies -/





open Catalog.NET68 in
theorem solution: codeLaw.eval 0 = 12 ∧ codeLaw.eval 1 = 16 := by
  constructor <;> norm_num [codeLaw, BudgetLaw.eval]
