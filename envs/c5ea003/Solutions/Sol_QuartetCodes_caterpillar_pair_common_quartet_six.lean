-- Prove2me | solution 1 for QuartetCodes.caterpillar_pair_common_quartet_six
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T22:56:56.826038+00:00
-- url     : https://prove2.me/submissions/fe2da782-aded-4f1f-aad5-4d1c98868433

-- Sol generated from Combinatorics/QuartetCodesSharpPair.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesSharpPair
import Theorems.Thm_QuartetCodes_qcode_restrict

/-!
# The two-tree quartet threshold is exactly six leaves

`Combinatorics.QuartetCodesUpperBound` shows by Erdős–Szekeres that any two caterpillars on ten
leaves share a quartet, while `QuartetCodes.not_isAgreementThreshold_five_two` exhibits two
caterpillars on five leaves sharing none.  Here the upper end is pushed down to the truth: **six**
leaves already force a common quartet, so the two-tree threshold is exactly `6`.

The proof is the coding-theoretic restriction principle in action.  A quartet letter depends only on
the *relative order* of the four leaves, so restricting a leaf order to any six leaves produces a
genuine six-leaf codeword (`qcode_restrict`), and a six-leaf statement transfers to every larger
leaf set.  The six-leaf statement itself is reduced by the group action
`(π, ρ) ↦ (1, ρ π⁻¹)` to a single quantifier over `Sym(6)` and then decided by the kernel.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Exhaustive computation says that all `720²` pairs of six-leaf caterpillars share a quartet, i.e.
`h(2) = 6`; the Erdős–Szekeres value `10` is an artefact of the proof method.

## Experiment (Experimenter)
Deciding `∀ π ρ : Sym(6), ∃ quartet` directly is `518400` pairs and is out of kernel reach.  Using
the right translation action of `Sym(6)` on pairs, the statement collapses to `720` cases
(`six_leaf_core`), which the kernel checks in about two minutes.  The transfer to `n ≥ 6` leaves
needs the rank permutation of an injective map (`rankPerm`) and the order-invariance of the ternary
letter (`code3_congr`).

## Analysis (Analyst)
The gain (from `10` down to `6`) comes entirely from *not* using Erdős–Szekeres: the quartet letter
is an order invariant, so a purely local six-leaf obstruction suffices.  The same mechanism should
sharpen the `k`-tree bound `3^{2^k}` if the corresponding finite statement can be decided for the
relevant window size.

## Critique (Critic)
`code3_congr` is stated with all twelve order comparisons, so it does not silently assume the four
leaves are distinct; `rankPerm` is built from an explicit rank function with a proved injectivity,
so the statement uses no choice beyond what `Equiv.ofBijective` needs.  The final theorem quantifies
over *all* pairs of leaf orders on *all* `n ≥ 6`, and the exhibited quartet is genuinely made of
four distinct leaves.
-/

open Finset

open QuartetCodes


variable {m n : ℕ}











lemma qcode_perm_comp {m : ℕ} (τ σ : Equiv.Perm (Fin m)) (x y z w : Fin m) :
    qcode τ (σ x) (σ y) (σ z) (σ w) = qcode (τ * σ) x y z w := by
  simp [qcode, Equiv.Perm.mul_apply]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
/-- The decided core: every leaf order on six leaves shares a quartet with the identity order. -/
theorem six_leaf_core : ∀ υ : Equiv.Perm (Fin 6), ∃ a b c d : Fin 6,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    qcode (1 : Equiv.Perm (Fin 6)) a b c d = qcode υ a b c d := by decide

/-- Any two leaf orders on six leaves share a quartet. -/
theorem six_leaf_pair (σ τ : Equiv.Perm (Fin 6)) :
    ∃ a b c d : Fin 6, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      qcode σ a b c d = qcode τ a b c d := by
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hcode⟩ := six_leaf_core (τ * σ⁻¹)
  refine ⟨σ⁻¹ x, σ⁻¹ y, σ⁻¹ z, σ⁻¹ w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hxy (σ⁻¹.injective h)
  · exact fun h => hxz (σ⁻¹.injective h)
  · exact fun h => hxw (σ⁻¹.injective h)
  · exact fun h => hyz (σ⁻¹.injective h)
  · exact fun h => hyw (σ⁻¹.injective h)
  · exact fun h => hzw (σ⁻¹.injective h)
  · rw [qcode_perm_comp σ σ⁻¹, qcode_perm_comp τ σ⁻¹, mul_inv_cancel]
    exact hcode




open QuartetCodes in
theorem solution{n : ℕ} (hn : 6 ≤ n) (π ρ : Equiv.Perm (Fin n)) :
    ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      qcode π a b c d = qcode ρ a b c d := by
  have hf : Function.Injective (Fin.castLE hn : Fin 6 → Fin n) := Fin.castLE_injective hn
  obtain ⟨σ, hσ⟩ := qcode_restrict π (Fin.castLE hn) hf
  obtain ⟨τ, hτ⟩ := qcode_restrict ρ (Fin.castLE hn) hf
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hcode⟩ := six_leaf_pair σ τ
  refine ⟨Fin.castLE hn a, Fin.castLE hn b, Fin.castLE hn c, Fin.castLE hn d, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact fun h => hab (hf h)
  · exact fun h => hac (hf h)
  · exact fun h => had (hf h)
  · exact fun h => hbc (hf h)
  · exact fun h => hbd (hf h)
  · exact fun h => hcd (hf h)
  · rw [hσ a b c d, hτ a b c d]; exact hcode
