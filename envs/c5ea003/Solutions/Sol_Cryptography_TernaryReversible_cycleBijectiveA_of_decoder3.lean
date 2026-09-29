-- Prove2me | solution 1 for Cryptography.TernaryReversible.cycleBijectiveA_of_decoder3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T00:25:08.740043+00:00
-- url     : https://prove2.me/submissions/8524bec5-30d8-49fd-a19c-672ad0d3dfc4

import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core
import Definitions.Def_Cryptography_TernaryReversible_General

set_option maxHeartbeats 1000000 in
open Cryptography TernaryReversible in
theorem solution {A : Type} [Fintype A] (g d : A → A → A → A)
    (h : ∀ v w x y z, d (g v w x) (g w x y) (g x y z) = x) : CycleBijectiveA g := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← Finite.injective_iff_bijective]
  -- the decoder reads the original cell off three consecutive output cells
  have key : ∀ (t : ZMod n → A) (j : ZMod n),
      d (globalMapA g t (j - 1)) (globalMapA g t j) (globalMapA g t (j + 1)) = t j := by
    intro t j
    show d (g (t (j - 1 - 1)) (t (j - 1)) (t (j - 1 + 1))) (g (t (j - 1)) (t j) (t (j + 1)))
        (g (t (j + 1 - 1)) (t (j + 1)) (t (j + 1 + 1))) = t j
    rw [show j - 1 + 1 = j by ring, show j + 1 - 1 = j by ring]
    exact h (t (j - 1 - 1)) (t (j - 1)) (t j) (t (j + 1)) (t (j + 1 + 1))
  intro s s' hss
  funext i
  rw [← key s i, ← key s' i, hss]
