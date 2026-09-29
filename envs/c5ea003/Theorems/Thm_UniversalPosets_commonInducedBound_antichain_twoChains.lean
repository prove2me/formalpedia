-- Prove2me | Theorems.Thm_UniversalPosets_commonInducedBound_antichain_twoChains
-- name    : UniversalPosets.commonInducedBound_antichain_twoChains
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:05:16.807228+00:00
-- url     : https://prove2.me/theorems/b6ff526c-b462-4418-b712-7a88458fad09
-- title:
--   An antichain and two disjoint chains share at most two points: an antichain
-- statement:
--   An antichain and two disjoint chains share at most two points: an antichain
--   inside `twoChains` has at most one point on each side.
--
--   ```lean
--   theorem UniversalPosets.commonInducedBound_antichain_twoChains(n : ℕ) :
--       CommonInducedBound (fun x y : Fin n => x = y) (twoChains n) 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/UniversalPosets/ThreePosetBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/UniversalPosets/ThreePosetBound.lean#L159

-- Thm stub generated from Cryptography/UniversalPosets/ThreePosetBound.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_ThreePosetBound

/-!
# A three-poset overlap bound: `U(n) ≥ 3n - ⌈n/2⌉ - 3`

`ExactSmall.lean` proved `2n - 1 ≤ U(n)` by playing the `n`-chain against the
`n`-antichain: two induced copies of posets with no large common induced
subposet cannot overlap much inside a host.  Here the method is pushed to a
*third* poset, the disjoint union of two chains of lengths `⌈n/2⌉` and `⌊n/2⌋`
(`twoChains`), whose common induced subposets with the chain and with the
antichain have at most `⌈n/2⌉` and `2` points respectively.  Bonferroni's
inequality for three sets then gives

`3n - (1 + ⌈n/2⌉ + 2) ≤ U(n)`,

i.e. asymptotically `U(n) ≥ 5n/2 - 3`, which improves `2n - 1` from `n = 6` on
(and agrees with it for `n ≤ 5`, where the earlier bound is already sharp for
`n ≤ 3`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  The overlap method is not limited to two posets: any
family `P₁,…,P_k` gives `U(n) ≥ kn - Σ_{i<j} s_{ij}` where `s_{ij}` bounds the
common induced subposets.  The optimisation is a genuine extremal problem; the
first nontrivial instance is `k = 3` with chain, antichain, and two chains.

Experiment (Experimenter).  Numerically, `3n - ⌈n/2⌉ - 3` beats `2n - 1` exactly
for `n ≥ 6` (`n = 6`: `12` versus `11`; `n = 10`: `22` versus `19`); both are
dwarfed by the counting bound `2^{(n-1)/4}` from about `n = 24` on.  Adding a
fourth poset was tested on paper and does *not* help: any fourth `n`-element
poset has a chain or an antichain of size at least `√n`, and its overlaps with
the three posets above already exceed the `n` points it contributes.

Analysis (Analyst).  The method is intrinsically linear: `k` posets contribute
`kn` but a fixed pair contributes an overlap at least `Ω(log n)` by
Dilworth/Erdős–Szekeres, and for large `k` the sum of overlaps dominates.  So no
choice of family can push the overlap method past `O(n log n)`; the exponential
lower bound must come from counting, as it does in `LogBounds.lean`.

Critique (Critic).  The bound is stated with truncated natural subtraction, so it
is vacuously weak for very small `n` and no hypothesis `n ≥ 6` is needed; the
sharper claim (that it *improves* on `2n-1`) is a numerical remark, not a
theorem, and is left to the table above.
-/

open UniversalPosets

open Function

/-! ## Bonferroni for three finsets -/


/-! ## The third poset: two disjoint chains -/






/-! ## The two new overlap bounds -/

theorem UniversalPosets.commonInducedBound_antichain_twoChains(n : ℕ) :
    CommonInducedBound (fun x y : Fin n => x = y) (twoChains n) 2 := by sorry
