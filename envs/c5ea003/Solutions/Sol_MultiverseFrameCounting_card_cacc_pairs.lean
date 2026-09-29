-- Prove2me | solution 1 for MultiverseFrameCounting.card_cacc_pairs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:39:50.521796+00:00
-- url     : https://prove2.me/submissions/0747b5f2-a2e0-4940-923c-3526a6783232

-- Sol generated from Logic/Multiverse/FrameCounting.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_FrameCounting
import Theorems.Thm_MultiverseFrameCounting_sum_two_pow_card_powerset
/-
# Counting the Finite Control Frames

A combinatorial companion to `Catalog/Logic/Multiverse/BooleanValuedRealization.lean`.

The finite pre-Boolean forcing frames used for the countermodels are assembled from
`n` independent buttons and `m` independent switches.  We compute their size
exactly:

* `sum_two_pow_card_powerset` — `∑_{t ⊆ s} 2^|t| = 3^|s|`, proved by induction on
  `s` (the enumerative heart: each element is either outside `t`, inside `t` but
  outside the ambient set, or in both);
* `card_cacc_pairs` — the frame with `n` buttons and `m` switches has exactly
  `3^n · 4^m` accessibility pairs, and (`card_worlds`) `2^(n+m)` worlds.

The count `3^n · 4^m` is exactly what an independent enumeration of the frames
produces (see `ComputationalEvidence.md`), and it exhibits the accessibility
relation as a *product* of `n` three-element button orders with `m` complete
two-element switch relations — the combinatorial form of the statement that buttons
and switches act independently.
-/

open MultiverseFrameCounting

open BooleanValuedRealization Finset

variable {α : Type*} [DecidableEq α]




/-- For a fixed world, the set of worlds it is accessible *from* is a product of a
powerset with the full set of switch settings. -/
theorem filter_cacc_eq (n m : ℕ) (v : CWorld (Fin n) (Fin m)) :
    (Finset.univ.filter fun w : CWorld (Fin n) (Fin m) => cacc w v)
      = v.1.powerset ×ˢ (Finset.univ : Finset (Fin m → Bool)) := by
  ext w
  simp [cacc, Finset.mem_powerset]



open MultiverseFrameCounting in
theorem solution(n m : ℕ) :
    ∑ v : CWorld (Fin n) (Fin m),
        (Finset.univ.filter fun w : CWorld (Fin n) (Fin m) => cacc w v).card
      = 3 ^ n * 4 ^ m := by
  have hcard : ∀ v : CWorld (Fin n) (Fin m),
      (Finset.univ.filter fun w : CWorld (Fin n) (Fin m) => cacc w v).card
        = 2 ^ v.1.card * 2 ^ m := by
    intro v
    rw [filter_cacc_eq n m v, Finset.card_product, Finset.card_powerset,
      Finset.card_univ]
    simp
  simp only [hcard]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ S : Finset (Fin n),
      ∑ _g : Fin m → Bool, 2 ^ S.card * 2 ^ m = 2 ^ S.card * 4 ^ m := by
    intro S
    rw [Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, smul_eq_mul,
      ← pow_add]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  simp only [hinner]
  rw [← Finset.sum_mul]
  congr 1
  have : (Finset.univ : Finset (Finset (Fin n))) = (Finset.univ : Finset (Fin n)).powerset := by
    simp [Finset.powerset_univ]
  rw [this, sum_two_pow_card_powerset, Finset.card_univ, Fintype.card_fin]
