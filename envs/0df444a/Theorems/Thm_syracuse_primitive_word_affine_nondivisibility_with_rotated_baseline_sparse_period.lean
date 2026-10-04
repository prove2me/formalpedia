-- Prove2me | Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline_sparse_period
-- name    : syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline_sparse_period
-- status  : Open
-- author  : @FakeMink
-- created : 2026-10-02T17:23:39.793771+00:00
-- url     : https://prove2.me/theorems/0ddfc585-79b5-4904-8288-32ed0e3bd173
-- title:
--   Remaining rotated-baseline primitive-word nondivisibility at sparse certified-budget periods
-- statement:
--   Let $w=(e_0,\ldots,e_{p-1})$ be a list of positive natural numbers, with $p=\operatorname{length}(w)\ge6291$ and $K=\sum_i e_i$. Assume every proper positive cyclic rotation differs from $w$. Define the canonical affine constant by
--
--   $$C([])=0,\qquad C(a::b)=3^{\operatorname{length}(b)}+2^a C(b).$$
--
--   Retain the power gap, both strict mean conditions, and the exact global budget at $B=2310000$:
--
--   $$3^p<2^K,\qquad200K<317p,\qquad306K<485p,\qquad2^K B^p\le(3B+1)^p.$$
--
--   Put $D=2^K-3^p>0$. Assume additionally that every indexed rotation meets the word-dependent certified-baseline filter:
--
--   $$\forall d\in\{0,\ldots,p-1\},\qquad BD\le C(w.rotate\ d).$$
--
--   Prove
--
--   $$D\nmid C(w).$$
--
--   This is an unresolved restricted arithmetic obligation. The new filter is an explicit premise on arbitrary candidate words, not an assertion that they automatically satisfy it. Its necessity for nontrivial realized cycles follows from a separately Proved finite cycle-state baseline and exact affine divisibility realization. No actual cycle is assumed before divisibility, no larger uncertified baseline is used, and no state upper bound or period cap is introduced. The remaining family and Collatz convergence are not claimed proved.
--
--   Additionally assume the explicitly tracked sparse-period premise p=6291 or p≥6956. Keep every original positivity, length, primitivity, power-gap, both low-mean, exact2310000-budget and every-rotation baseline premise unchanged. Prove the same affine nondivisibility conclusion. This remains an OPEN arithmetic obligation; the added premise removes no case permitted by the parent's already explicit gap and budget, by the separately public Proved arithmetic sparse-period theorem. It excludes exactly the664 integer periods6292 through6955 under those premises, not unconditionally. The hard period6291 and the unbounded tail p≥6956 remain unresolved. No state upper bound, period cap, larger baseline or new mean premise is introduced. This source-only child has no assigned public UUID and is not yet registered or Proved.
-- source:
--   Task102 source-only prospective tracked Open refinement of saved peer-reported parent https://prove2.me/theorems/9f28e7b8-804f-4efd-83e3-1e68362b2b34; exact parent type/preamble from problem_rotated_state_v01.json SHA256c70347226787f15c9ef33bec06231dc3082134fa21e978d794c2d0fe3fb33b68. Uses saved public Proved sparse arithmetic helper https://prove2.me/theorems/86d6ebd5-f48c-4488-ad86-577e76e9b0b1 (ACCEPTED148bed53-8007-4529-90a5-00c1158db5de, actual saved145-line readback SHA25621d0a88f88714dc3e2c05a471728ae7358e1f323fdd804bc76ed0ae666cc66b1 and independent MAIN saved acceptance audit). Credits prior rotation-filter sketch26ec230a-e6f3-4394-ab2b-3cc335cd34ad and canonical Offset definition https://prove2.me/theorems/864533ea-15c3-4810-a04c-d66a460333b7. The complementary source proves only the period disjunction and explicitly imports this unresolved prospective child; it is a proof-SKETCH, not a completed arithmetic, parent, tail or Collatz proof. All status/frontier observations are saved evidence, not a fresh API audit by this producer. Sparse empty decomposition is ATTRIBUTION_MISSING, not a dependency PASS. No accepted-source equality or full transitive/axiom audit is asserted for sparse helper. No public write or runtime authority is supplied.

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline_sparse_period (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6291 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2310000 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d))
    (hsparsePeriod : w.length = 6291 ∨ 6956 ≤ w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
