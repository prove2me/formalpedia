-- Prove2me | solution 1 for QuartetCodes.eight_mul_card_image_sigD_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:32:09.409975+00:00
-- url     : https://prove2.me/submissions/1708d98b-9825-4ab6-a0b1-f0a1f988c1b9

-- Sol generated from Combinatorics/QuartetCodesIndexEight.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesIndexEight
import Definitions.Def_Combinatorics_QuartetCodesRate
import Theorems.Thm_QuartetCodes_sigD_lowSwap
import Theorems.Thm_QuartetCodes_sigD_rev

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











/-- Every one of the eight symmetries preserves the signature. -/
theorem sigD_symm8 (hn : 4 ≤ n) (i : Fin 8) (π : Equiv.Perm (Fin n)) :
    sigD ((symm8 hn i) * π) = sigD π := by
  have ha : ∀ σ : Equiv.Perm (Fin n), sigD ((lowSwap hn) * σ) = sigD σ := sigD_lowSwap hn
  have hr : ∀ σ : Equiv.Perm (Fin n),
      sigD ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) = sigD σ := sigD_rev
  fin_cases i <;> simp only [symm8] <;> simp [ha, hr, mul_assoc]

lemma revPerm_apply_val (v : Fin n) :
    ((Fin.revPerm : Equiv.Perm (Fin n)) v).val = n - 1 - v.val := by
  simp [Fin.val_rev]
  omega


lemma lowSwap_apply_zero (hn : 4 ≤ n) :
    (lowSwap hn) ⟨0, by omega⟩ = ⟨1, by omega⟩ := Equiv.swap_apply_left _ _


lemma lowSwap_apply_of_val_ne (hn : 4 ≤ n) (v : Fin n) (h0 : v.val ≠ 0) (h1 : v.val ≠ 1) :
    (lowSwap hn) v = v :=
  Equiv.swap_apply_of_ne_of_ne (fun h => h0 (by rw [h])) (fun h => h1 (by rw [h]))

lemma revPerm_apply_mk (k : ℕ) (hk : k < n) :
    (Fin.revPerm : Equiv.Perm (Fin n)) ⟨k, hk⟩ = ⟨n - 1 - k, by omega⟩ := by
  apply Fin.ext
  rw [revPerm_apply_val]

/-- The eight symmetries evaluated at the first and last position. -/
lemma evalEnds_symm8 (hn : 4 ≤ n) (i : Fin 8) :
    evalEnds hn (symm8 hn i) =
      ![(0, n - 1), (1, n - 1), (0, n - 2), (1, n - 2), (n - 1, 0), (n - 2, 0), (n - 1, 1),
        (n - 2, 1)] i := by
  have hrev : ∀ k (hk : k < n),
      (Fin.revPerm : Equiv.Perm (Fin n)) ⟨k, hk⟩ = ⟨n - 1 - k, by omega⟩ := revPerm_apply_mk
  have hlast : (lowSwap hn) ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩ :=
    lowSwap_apply_of_val_ne hn _ (by simp; omega) (by simp; omega)
  have hn2 : (lowSwap hn) ⟨n - 2, by omega⟩ = ⟨n - 2, by omega⟩ :=
    lowSwap_apply_of_val_ne hn _ (by simp; omega) (by simp; omega)
  fin_cases i <;> simp only [symm8, evalEnds] <;>
    simp [hrev, hlast, hn2, lowSwap_apply_zero hn,
      show n - 1 - 1 = n - 2 from by omega] <;> omega

set_option maxRecDepth 100000 in
lemma symm8_injective (hn : 4 ≤ n) : Function.Injective (symm8 hn) := by
  intro i j hij
  have h := congrArg (evalEnds hn) hij
  rw [evalEnds_symm8 hn i, evalEnds_symm8 hn j] at h
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; simp [Prod.ext_iff] at h; try omega)




open QuartetCodes in
theorem solution(hn : 4 ≤ n) :
    8 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD).card ≤ Nat.factorial n := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := (sigD : Equiv.Perm (Fin n) → _))
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (t := (Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD)
    (fun x _ => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
  have hcards : ∀ w ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD,
      8 ≤ {σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) | sigD σ = w}.card := by
    intro w hw
    obtain ⟨π, -, hπ⟩ := Finset.mem_image.1 hw
    have hinj : Function.Injective (fun i : Fin 8 => (symm8 hn i) * π) := by
      intro i j hij
      exact symm8_injective hn (mul_right_cancel hij)
    have hsub : (Finset.univ : Finset (Fin 8)).image (fun i => (symm8 hn i) * π)
        ⊆ {σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) | sigD σ = w} := by
      intro σ hσ
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hσ
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [sigD_symm8 hn i π]; exact hπ⟩
    calc (8 : ℕ) = ((Finset.univ : Finset (Fin 8)).image (fun i => (symm8 hn i) * π)).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card hsub
  have hsum : 8 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD).card
      ≤ ∑ w ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD,
          {σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) | sigD σ = w}.card := by
    calc 8 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD).card
        = ∑ _w ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).image sigD, 8 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hcards
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    simp [Finset.card_univ, Fintype.card_perm]
  omega
