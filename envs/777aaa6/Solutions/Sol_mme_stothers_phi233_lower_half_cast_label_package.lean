-- Prove2me | solution 1 for mme_stothers_phi233_lower_half_cast_label_package
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:24:44.779741+00:00
-- url     : https://prove2.me/submissions/3621cb83-fa0d-4775-b2b0-f7c52b9f0588

import Theorems.Thm_mme_lower_half_ZMod_image_card
import Theorems.Thm_mme_dwz_threeAP_free_cast_labels_collapse

set_option autoImplicit false

theorem solution
    (p : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
    let castS := S.image (fun s : ℕ => (s : ZMod p))
    castS.card = S.card ∧
      ∀ a ∈ castS, ∀ b ∈ castS, ∀ c ∈ castS,
        a + b = 2 * c → a = c ∧ c = b := by
  dsimp only
  constructor
  · exact mme_lower_half_ZMod_image_card p S hSrange
  · intro a ha b hb c hc hAP
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hc with ⟨z, hz, rfl⟩
    obtain ⟨hxz, hzy⟩ :=
      mme_dwz_threeAP_free_cast_labels_collapse
        p S hSrange hSfree x y z hx hy hz hAP
    exact ⟨congrArg (fun n : ℕ => (n : ZMod p)) hxz,
      congrArg (fun n : ℕ => (n : ZMod p)) hzy⟩
