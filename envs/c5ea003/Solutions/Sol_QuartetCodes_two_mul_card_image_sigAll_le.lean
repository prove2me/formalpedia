-- Prove2me | solution 1 for QuartetCodes.two_mul_card_image_sigAll_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:02:14.562096+00:00
-- url     : https://prove2.me/submissions/7b130f1d-d774-45bd-901c-2f536efda275

-- Sol generated from Combinatorics/QuartetCodesRate.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesRate
import Theorems.Thm_QuartetCodes_code3_rev
import Theorems.Thm_QuartetCodes_revPerm_mul_ne

/-!
# The caterpillar quartet code is at most half of the leaf orders

The quartet signature of a caterpillar is invariant under reversing the leaf order — an unrooted
tree does not remember which end of the caterpillar is first.  Consequently the *code* (the image
of the signature map inside the ternary cube) has at most `n!/2` words, which is the packing
statement complementing the lower-bound construction of `Combinatorics.QuartetCodes`: the trees
one may pick from are the codewords, and there are at most `n!/2` of them, while the ambient
ternary space has `3^(n choose 4)` points.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Reversal is a symmetry of the quartet signature, so the signature map is at least two-to-one; more
symmetries (swapping the first two, resp. last two, leaves) should push the index to `8`, and the
five-leaf computation in `Combinatorics.QuartetCodesConsistency` (`15 = 5!/8`) says the index is
exactly `8`.

## Experiment (Experimenter)
The reversal invariance is proved here for *all* quadruples, degenerate ones included, because the
reversal `v ↦ N - v` flips every comparison at once.  (The other two symmetries genuinely need the
four leaves to be distinct: for the value transposition `0 ↔ 1` the degenerate quadruple
`(0,0,1,5)` changes its type, so those symmetries only act on the non-degenerate part.)

## Analysis (Analyst)
The index-2 bound is what a *global* symmetry gives; the remaining factor `4` comes from the two
local cherry symmetries at the ends of the caterpillar and is visible in the exact five-leaf count.

## Critique (Critic)
The bound is stated for the full signature function (all ordered quadruples), so it is a statement
about a concrete finite code and not about an equivalence class chosen for convenience.
-/

open Finset

open QuartetCodes


variable {n : ℕ}



/-- **Reversal symmetry.**  Reversing the leaf order does not change the quartet signature. -/
theorem sigAll_rev (π : Equiv.Perm (Fin n)) :
    sigAll (Fin.revPerm * π) = sigAll π := by
  funext q
  obtain ⟨a, b, c, d⟩ := q
  have hval : ∀ x : Fin n, ((Fin.revPerm * π : Equiv.Perm (Fin n)) x).val = n - 1 - (π x).val := by
    intro x
    simp [Equiv.Perm.mul_apply, Fin.val_rev]
    omega
  have hle : ∀ x : Fin n, (π x).val ≤ n - 1 := fun x => Nat.le_pred_of_lt (π x).isLt
  show code3 _ _ _ _ = code3 _ _ _ _
  rw [hval a, hval b, hval c, hval d]
  exact code3_rev (hle a) (hle b) (hle c) (hle d)





open QuartetCodes in
theorem solution(hn : 2 ≤ n) :
    2 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).image sigAll).card
      ≤ Nat.factorial n := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := (sigAll : Equiv.Perm (Fin n) → _))
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (t := (Finset.univ : Finset (Equiv.Perm (Fin n))).image sigAll)
    (fun x _ => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
  have hcards : ∀ w ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).image sigAll,
      2 ≤ {π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) | sigAll π = w}.card := by
    intro w hw
    obtain ⟨π, -, hπ⟩ := Finset.mem_image.1 hw
    have hsub : ({π, Fin.revPerm * π} : Finset (Equiv.Perm (Fin n)))
        ⊆ {σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) | sigAll σ = w} := by
      intro σ hσ
      rcases Finset.mem_insert.1 hσ with rfl | hσ'
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hπ⟩
      · rw [Finset.mem_singleton] at hσ'
        subst hσ'
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [sigAll_rev]; exact hπ⟩
    have hpair : ({π, Fin.revPerm * π} : Finset (Equiv.Perm (Fin n))).card = 2 :=
      Finset.card_pair (Ne.symm (revPerm_mul_ne hn π))
    calc 2 = ({π, Fin.revPerm * π} : Finset (Equiv.Perm (Fin n))).card := hpair.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hsum : 2 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).image sigAll).card
      ≤ ∑ w ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).image sigAll,
          {π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) | sigAll π = w}.card := by
    calc 2 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).image sigAll).card
        = ∑ _w ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).image sigAll, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hcards
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    simp [Finset.card_univ, Fintype.card_perm]
  omega
