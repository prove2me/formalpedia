-- Prove2me | solution 1 for QuartetCodes.sigD_lowSwap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:05:19.7553+00:00
-- url     : https://prove2.me/submissions/ff56c37b-c927-4c2c-924e-745823e89294

-- Sol generated from Combinatorics/QuartetCodesIndexEight.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesIndexEight
import Definitions.Def_Combinatorics_QuartetCodesRate
import Theorems.Thm_QuartetCodes_perm_val_ne

/-!
# The caterpillar quartet code has at most `n!/8` codewords

`Combinatorics.QuartetCodesRate` proves the packing bound `2 · #code ≤ n!` from the reversal
symmetry of a caterpillar.  Here the bound is improved to the conjecturally exact index,
`8 · #code ≤ n!`, by adding the two *cherry* symmetries: exchanging the two leaves at either end of
the caterpillar does not change any quartet.

Because a degenerate quadruple (one with a repeated leaf) is *not* invariant under the cherry
symmetry, the signature used here is the honest one: it is the quartet letter on quadruples of
pairwise distinct leaves and a fixed dummy value elsewhere (`sigD`).

The three generators are reversal `r`, the exchange `a` of the two lowest positions, and
`b = r * a * r`, the exchange of the two highest positions.  Their eight products are pairwise
distinct as soon as `n ≥ 4`, which is verified by evaluating each of them at the first and the last
leaf position.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
The quartet-signature fibres of `Sym(n)` have size exactly `8`; the computation in
`ComputationalEvidence.md` confirms this for `n = 4, 5, 6, 7`, and `card_image_sig5 = 15 = 5!/8`
confirms it formally at `n = 5`.  The `≤ n!/8` half should be provable for all `n` by exhibiting
the eight symmetries.

## Experiment (Experimenter)
The delicate point is the cherry symmetry: swapping the two *values* `0` and `1` flips the
comparison between the leaves carrying them, so the order-congruence lemma `code3_congr` does not
apply.  Instead the invariance is proved by direct case analysis (`code3_sw01`, ~1000 branches
discharged by `omega`), which is valid precisely because the two swapped values are the two global
minima and therefore stay the "low pair" of every quadruple containing both.

## Analysis (Analyst)
The three symmetries are the automorphisms of an unrooted caterpillar, and the argument shows they
act freely on `Sym(n)`, giving the packing bound `8 · #code ≤ n!`.  The converse inequality —
identifiability of the caterpillar from its quartets up to these eight relabellings — is the open
half recorded in `FUTURE_DIRECTIONS.md`.

## Critique (Critic)
Invariance is stated for the signature on *all* quadruples with a dummy value on degenerate ones, so
the theorem is about a genuine finite code, and no quadruple is quietly excluded.  The eight
symmetries are proved pairwise distinct for every `n ≥ 4`, not just for small `n`.
-/

open Finset

open QuartetCodes


variable {n : ℕ}


set_option maxHeartbeats 2000000 in
/-- Exchanging the two smallest positions does not change the quartet type of four distinct
leaves. -/
lemma code3_sw01 {p q r s : ℕ} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    code3 (sw01 p) (sw01 q) (sw01 r) (sw01 s) = code3 p q r s := by
  unfold code3 sw01
  split_ifs <;> first | rfl | (exfalso; omega)





lemma lowSwap_val (hn : 4 ≤ n) (v : Fin n) : ((lowSwap hn) v).val = sw01 v.val := by
  unfold lowSwap sw01
  by_cases h0 : v = (⟨0, by omega⟩ : Fin n)
  · subst h0; rw [Equiv.swap_apply_left]; simp
  · by_cases h1 : v = (⟨1, by omega⟩ : Fin n)
    · subst h1; rw [Equiv.swap_apply_right]; simp
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
      have hv0 : v.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hv1 : v.val ≠ 1 := fun h => h1 (Fin.ext h)
      simp [hv0, hv1]
















open QuartetCodes in
theorem solution(hn : 4 ≤ n) (π : Equiv.Perm (Fin n)) :
    sigD ((lowSwap hn) * π) = sigD π := by
  funext q
  obtain ⟨a, b, c, d⟩ := q
  unfold sigD
  by_cases hq : QuadDistinct ((a, b, c, d) : Fin n × Fin n × Fin n × Fin n)
  · simp only [hq, if_true]
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hq
    have hval : ∀ x : Fin n, (((lowSwap hn) * π : Equiv.Perm (Fin n)) x).val = sw01 (π x).val := by
      intro x
      rw [Equiv.Perm.mul_apply, lowSwap_val]
    show code3 _ _ _ _ = code3 _ _ _ _
    rw [hval a, hval b, hval c, hval d]
    exact code3_sw01 (perm_val_ne hab) (perm_val_ne hac) (perm_val_ne had) (perm_val_ne hbc)
      (perm_val_ne hbd) (perm_val_ne hcd)
  · simp [hq]
