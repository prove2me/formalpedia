-- Prove2me | solution 1 for SingularModuli.rootCount_le_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:02:28.227714+00:00
-- url     : https://prove2.me/submissions/9f019d17-937d-4a8a-9e73-103737211921

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount

open SingularModuli

open Polynomial Finset FactoringBarriers

namespace SingularModuli

theorem solution (H : Polynomial ℤ) {m : ℕ} (hm : m.Prime) (hH : H.Monic) :
    haveI : NeZero m := ⟨hm.pos.ne'⟩
    rootCount H m ≤ H.natDegree := by
  haveI : Fact m.Prime := ⟨hm⟩
  haveI : NeZero m := ⟨hm.pos.ne'⟩
  have hmonic : (redMod H m).Monic := hH.map _
  have hne : redMod H m ≠ 0 := hmonic.ne_zero
  have hndeg : (redMod H m).natDegree = H.natDegree := hH.natDegree_map _
  calc (rootFinset H m).card = (redMod H m).roots.toFinset.card := by
        congr 1
        ext x
        simp only [rootFinset, Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
          Polynomial.mem_roots hne]
        exact Iff.rfl
    _ ≤ (redMod H m).roots.card := Multiset.toFinset_card_le _
    _ ≤ (redMod H m).natDegree := Polynomial.card_roots' _
    _ = H.natDegree := hndeg

end SingularModuli

open SingularModuli

theorem solution (H : Polynomial ℤ) {m : ℕ} (hm : m.Prime) (hH : H.Monic) :
    haveI : NeZero m := ⟨hm.pos.ne'⟩
    rootCount H m ≤ H.natDegree :=
  SingularModuli.solution H hm hH

#print axioms solution
