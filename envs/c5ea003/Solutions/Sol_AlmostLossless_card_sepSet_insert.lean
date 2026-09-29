-- Prove2me | solution 1 for AlmostLossless.card_sepSet_insert
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:30:53.207688+00:00
-- url     : https://prove2.me/submissions/6f4058aa-f212-4e3b-8d00-1f6c6e6722fa

-- Sol generated from Geometry/AlmostLosslessExact.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Definitions.Def_Geometry_AlmostLosslessExact
/-
# The exact failure probability of random hashing

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

`AlmostLosslessDecoder` gives the upper bound `P[failure] ≤ (|S|-1)/M` and
`AlmostLosslessConverse` the Bonferroni lower bound `P[failure] ≥ (|S|-1)/(2M)`.
Here we compute the quantity **exactly**:

`AlmostLossless.card_sepSet` :  `M^k · |{H : H separates x from D}| = (M-1)^k · M^{|α|}`  (`k = |D|`),

whence `AlmostLossless.failure_prob_exact`:

`P[failure at x] = 1 - (1 - 1/M)^{|S|-1}`.

Both previously proved bounds are corollaries of this identity in the regime
they cover, and the measured values of `AlmostLosslessLabNotes` (`3/4`, `5/9`,
`7/16`, `15/64`, `31/256`) are exactly its values at `|S| = 3`.

The proof is an explicit bijection
`{H separating x from D ∪ {a}} × Fin M  ≃  Σ_{H separating x from D} (Fin M \ {H x})`,
given by `(H, v) ↦ ⟨update H a v, H a⟩`, iterated by induction on `D`.
-/

open AlmostLossless

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}








open AlmostLossless in
theorem solution{D : Finset α} {x a : α} (ha : a ∉ D) (hax : a ≠ x) :
    M * (sepSet (insert a D) x M).card = (M - 1) * (sepSet D x M).card := by
  classical
  have hbij : ((sepSet (insert a D) x M) ×ˢ (univ : Finset (Fin M))).card
      = ((sepSet D x M).sigma (fun H => (univ : Finset (Fin M)).erase (H x))).card := by
    apply Finset.card_bij (fun z _ => ⟨Function.update z.1 a z.2, z.1 a⟩)
    · rintro ⟨H, v⟩ hz
      rw [mem_product] at hz
      have hH : ∀ y ∈ insert a D, H y ≠ H x := by
        simpa [sepSet] using hz.1
      have hHa : H a ≠ H x := hH a (mem_insert_self a D)
      rw [Finset.mem_sigma]
      constructor
      · simp only [sepSet, mem_filter, mem_univ, true_and]
        intro y hy
        have hya : y ≠ a := fun h => ha (h ▸ hy)
        have hyx : x ≠ a := fun h => hax h.symm
        simpa [Function.update_apply, hya, hyx] using hH y (mem_insert_of_mem hy)
      · have hxa : x ≠ a := fun h => hax h.symm
        simp only [Finset.mem_erase, mem_univ, and_true]
        simpa [Function.update_apply, hxa] using hHa
    · rintro ⟨H, v⟩ hz ⟨H', v'⟩ hz' heq
      simp only [Sigma.mk.injEq] at heq
      have hHa : H a = H' a := eq_of_heq heq.2
      have hupd : Function.update H a v = Function.update H' a v' := heq.1
      have hv : v = v' := by
        have := congrArg (fun f => f a) hupd
        simpa using this
      have hHH : H = H' := by
        funext y
        rcases eq_or_ne y a with hy | hy
        · rw [hy, hHa]
        · have := congrArg (fun f => f y) hupd
          simpa [Function.update_apply, hy] using this
      simp [hHH, hv]
    · rintro ⟨H, w⟩ hz
      rw [Finset.mem_sigma] at hz
      have hH : ∀ y ∈ D, H y ≠ H x := by simpa [sepSet] using hz.1
      have hw : w ≠ H x := (Finset.mem_erase.1 hz.2).1
      have hxa : x ≠ a := fun h => hax h.symm
      refine ⟨(Function.update H a w, H a), ?_, ?_⟩
      · rw [mem_product]
        refine ⟨?_, mem_univ _⟩
        simp only [sepSet, mem_filter, mem_univ, true_and]
        intro y hy
        rcases Finset.mem_insert.1 hy with hy' | hy'
        · simpa [hy', Function.update_apply, hxa] using hw
        · have hya : y ≠ a := fun h => ha (h ▸ hy')
          simpa [Function.update_apply, hya, hxa] using hH y hy'
      · have h1 : Function.update (Function.update H a w) a (H a) = H := by
          funext y
          rcases eq_or_ne y a with hy | hy
          · rw [hy]; simp
          · simp [hy]
        simp [h1]
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_sigma] at hbij
  have hsum : ∑ H ∈ sepSet D x M, ((univ : Finset (Fin M)).erase (H x)).card
      = (sepSet D x M).card * (M - 1) := by
    rw [Finset.sum_congr rfl (fun H _ => by
      rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]),
      Finset.sum_const, smul_eq_mul]
  rw [hsum] at hbij
  calc M * (sepSet (insert a D) x M).card
      = (sepSet (insert a D) x M).card * M := by ring
    _ = (sepSet D x M).card * (M - 1) := hbij
    _ = (M - 1) * (sepSet D x M).card := by ring
