-- Prove2me | solution 2 for TwoTreeClosure.gaussBattery_letterBlind
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:36:54.821584+00:00
-- url     : https://prove2.me/submissions/d9212407-3c35-44ba-ab78-4c5e0c2baa81

import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_GaussDial
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
open TwoTreeClosure in
theorem solution (M : ℕ) (hM : 1 ≤ M) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ∣ M ∧ 0 < d) (G : (ℕ → ℂ) → Letter) :
    ¬ (∀ m n, IsNode m n → G (fun d => if d ∈ s then gaussSum d (hyp m n) else 0)
        = letterOf m n) := by
  intro hall
  -- `505 = 19² + 12² = 21² + 8²`: one hypotenuse, two nodes, letters `A` and `B`
  have n1 : IsNode 19 12 := ⟨by norm_num, by norm_num, by decide, by norm_num⟩
  have n2 : IsNode 21 8 := ⟨by norm_num, by norm_num, by decide, by norm_num⟩
  have hh : hyp 19 12 = hyp 21 8 := by norm_num [hyp]
  have h1 := hall 19 12 n1
  have h2 := hall 21 8 n2
  -- the dial reads the same data at both nodes, so it cannot output both letters
  rw [hh, h2] at h1
  exact absurd h1 (by decide)
