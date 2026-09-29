-- Prove2me | solution 1 for QuartetCodes.qcode_restrict
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T22:55:21.900961+00:00
-- url     : https://prove2.me/submissions/16d5d76b-0d84-45cf-8c13-c816d138d200

-- Sol generated from Combinatorics/QuartetCodesSharpPair.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesSharpPair

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

/-- The ternary quartet letter depends only on the order relations among the four positions. -/
lemma code3_congr {p q r s p' q' r' s' : ℕ}
    (hpq : p < q ↔ p' < q') (hqp : q < p ↔ q' < p')
    (hpr : p < r ↔ p' < r') (hrp : r < p ↔ r' < p')
    (hps : p < s ↔ p' < s') (hsp : s < p ↔ s' < p')
    (hqr : q < r ↔ q' < r') (hrq : r < q ↔ r' < q')
    (hqs : q < s ↔ q' < s') (hsq : s < q ↔ s' < q')
    (hrs : r < s ↔ r' < s') (hsr : s < r ↔ s' < r') :
    code3 p q r s = code3 p' q' r' s' := by
  unfold code3
  simp only [max_lt_iff, lt_min_iff, hpq, hqp, hpr, hrp, hps, hsp, hqr, hrq, hqs, hsq, hrs, hsr]




lemma rankOf_lt_iff {g : Fin m → Fin n} (hg : Function.Injective g) (i j : Fin m) :
    rankOf g i < rankOf g j ↔ (g i).val < (g j).val := by
  constructor
  · intro h
    rcases lt_trichotomy (g i).val (g j).val with hlt | heq | hgt
    · exact hlt
    · exact absurd (congrArg (rankOf g) (hg (Fin.val_injective heq))) (Nat.ne_of_lt h)
    · exact absurd (rankOf_lt_of_lt hgt) (asymm h)
  · exact rankOf_lt_of_lt


lemma rankPerm_val {g : Fin m → Fin n} (hg : Function.Injective g) (i : Fin m) :
    ((rankPerm g hg) i).val = rankOf g i := rfl










open QuartetCodes in
theorem solution(π : Equiv.Perm (Fin n)) (f : Fin m → Fin n)
    (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin m), ∀ a b c d : Fin m,
      qcode π (f a) (f b) (f c) (f d) = qcode σ a b c d := by
  have hg : Function.Injective (fun i : Fin m => π (f i)) :=
    fun x y hxy => hf (π.injective hxy)
  refine ⟨rankPerm (fun i => π (f i)) hg, ?_⟩
  intro a b c d
  have key : ∀ i j : Fin m,
      (π (f i)).val < (π (f j)).val ↔
        ((rankPerm (fun i => π (f i)) hg) i).val < ((rankPerm (fun i => π (f i)) hg) j).val := by
    intro i j
    rw [rankPerm_val, rankPerm_val]
    exact (rankOf_lt_iff hg i j).symm
  exact code3_congr (key a b) (key b a) (key a c) (key c a) (key a d) (key d a)
    (key b c) (key c b) (key b d) (key d b) (key c d) (key d c)
