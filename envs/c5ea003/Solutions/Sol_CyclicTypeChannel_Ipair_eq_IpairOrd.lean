-- Prove2me | solution 1 for CyclicTypeChannel.Ipair_eq_IpairOrd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:29:09.381983+00:00
-- url     : https://prove2.me/submissions/8b8f6597-01bf-4413-8a39-c1017fa2b0be

-- Sol generated from Shared/CyclicTypeChannelCRTLaw.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
import Theorems.Thm_CyclicTypeChannel_mutInfo_symPair
import Theorems.Thm_CyclicTypeChannel_prodRes_symm
/-
# The CRT additivity law for the splitting-type channel

The exact evaluations show an arithmetic law behind the numbers: for coprime
cyclic orders the type-pair channel is *additive*,

  `I_pair (m * n) = I_pair m + I_pair n`.

This file proves the law in general (for the ordered type pair) from three
ingredients:

* the Chinese Remainder Theorem, which relabels the sample set `CyclicTypeChannel.box (m*n)` as
  the product `CyclicTypeChannel.box m ×ˢ CyclicTypeChannel.box n`;
* the multiplicativity of the splitting type,
  `ord_{mn}(a) = ord_m(a) · ord_n(a)`, together with the fact that this
  factorisation is an *injective recoding* of the pair of component types;
* the additivity of the counting channel over independent products
  (`mutInfo_prod`).

The consequence is a structural explanation of the growth table:
the information of a cyclic order is a sum of primary contributions, so the
one-bit binary cap can be exceeded simply by multiplying orders together.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. The ordered type-pair channel -/




/-! ## 2. Multiplicativity of the splitting type -/



/-! ## 3. The CRT relabelling of the sample set -/





/-! ## 4. The additivity law -/


/-! ## 5. From the ordered to the unordered pair -/




/-! ## 6. The channel is determined by its prime-power values -/




open CyclicTypeChannel in
theorem solution(n : ℕ) : Ipair n = IpairOrd n := by
  have hσs : ∀ p ∈ CyclicTypeChannel.box n, Prod.swap p ∈ CyclicTypeChannel.box n := by
    intro p hp
    simp only [CyclicTypeChannel.box, mem_product, mem_range, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  have hσσ : ∀ p ∈ CyclicTypeChannel.box n, Prod.swap (Prod.swap p) = p := fun p _ => rfl
  have hgσ : ∀ p ∈ CyclicTypeChannel.box n, ordPair n (Prod.swap p) = ((ordPair n p).2, (ordPair n p).1) :=
    fun p _ => rfl
  have hkσ : ∀ p ∈ CyclicTypeChannel.box n, prodRes n (Prod.swap p) = prodRes n p := by
    intro p _
    exact prodRes_symm n p.2 p.1
  rw [Ipair, IpairOrd, show typePair n = symPair ∘ ordPair n from rfl]
  exact mutInfo_symPair hσs hσσ hgσ hkσ
