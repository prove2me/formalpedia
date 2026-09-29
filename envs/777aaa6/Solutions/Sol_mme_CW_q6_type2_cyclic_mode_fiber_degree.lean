-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_mode_fiber_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T09:51:13.902966+00:00
-- url     : https://prove2.me/submissions/2236ebb1-dc54-4b1c-91d8-3a15d5cfadbc

import Definitions.Def_mme_CW_q6_type2_cyclic_data
import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod

open MME

set_option autoImplicit false

noncomputable local instance solCoupledAddressFintype (N : ℕ) : Fintype (CWQ6CoupledAddress N) := inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))
noncomputable local instance solExactAddressFintype (N L G : ℕ) : Fintype (CWQ6ExactCoupledAddress N L G) := Fintype.ofInjective (fun e ↦ e.1) Subtype.val_injective
noncomputable local instance solExactAddressDecidableEq (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) := Classical.decEq _
noncomputable local instance solType2EdgeFintype (N L G : ℕ) : Fintype (CWQ6Type2CyclicEdge N L G) := inferInstanceAs (Fintype (CWQ6ExactCoupledAddress N L G × (CWQ6ExactCoupledAddress N L G × CWQ6ExactCoupledAddress N L G)))
noncomputable local instance solType2EdgeDecidableEq (N L G : ℕ) : DecidableEq (CWQ6Type2CyclicEdge N L G) := Classical.decEq _
noncomputable local instance solType2ModeWordDecidableEq (N : ℕ) : DecidableEq (CWQ6Type2CyclicModeWord N) := Classical.decEq _

lemma subtype_fiber_card (N L G : ℕ) (m : Fin 3) (w : Fin (2 * N) → Fin 3) :
    (Finset.univ.filter
        (fun a : CWQ6ExactCoupledAddress N L G => a.1 m = w)).card =
      ((cwQ6ExactAddresses N L G).filter (fun a => a m = w)).card := by
  classical
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a.2, ha⟩
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro b hb
    simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb.2

lemma val_mem_exact (N L G : ℕ) (a : CWQ6ExactCoupledAddress N L G) :
    a.1 ∈ cwQ6ExactAddresses N L G := by
  classical
  simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ, true_and]
  exact a.2

lemma fiber0 (N L G : ℕ) (hLG : L + G = N) (a : CWQ6ExactCoupledAddress N L G) :
    (Finset.univ.filter
      (fun f : CWQ6ExactCoupledAddress N L G => f.1 0 = a.1 0)).card
      = (Nat.choose N G) ^ (2 : ℕ) := by
  rw [subtype_fiber_card]
  exact (mme_CW_q6_exact_coupled_address_regularity N L G hLG).x_degree _
    (Finset.mem_image_of_mem _ (val_mem_exact N L G a))

lemma fiber1 (N L G : ℕ) (hLG : L + G = N) (a : CWQ6ExactCoupledAddress N L G) :
    (Finset.univ.filter
      (fun f : CWQ6ExactCoupledAddress N L G => f.1 1 = a.1 1)).card
      = (Nat.choose N G) ^ (2 : ℕ) := by
  rw [subtype_fiber_card]
  exact (mme_CW_q6_exact_coupled_address_regularity N L G hLG).y_degree _
    (Finset.mem_image_of_mem _ (val_mem_exact N L G a))

lemma fiber2 (N L G : ℕ) (hLG : L + G = N) (a : CWQ6ExactCoupledAddress N L G) :
    (Finset.univ.filter
      (fun f : CWQ6ExactCoupledAddress N L G => f.1 2 = a.1 2)).card
      = Nat.choose (2 * G) G := by
  rw [subtype_fiber_card]
  exact (mme_CW_q6_exact_coupled_address_regularity N L G hLG).z_degree _
    (Finset.mem_image_of_mem _ (val_mem_exact N L G a))

lemma edge_filter_card (N L G : ℕ) (m0 m1 m2 : Fin 3)
    (e : CWQ6Type2CyclicEdge N L G) :
    ((Finset.univ : Finset (CWQ6Type2CyclicEdge N L G)).filter
      (fun f => (f.1.1 m0, f.2.1.1 m1, f.2.2.1 m2)
        = (e.1.1 m0, e.2.1.1 m1, e.2.2.1 m2))).card
      = (Finset.univ.filter
            (fun a : CWQ6ExactCoupledAddress N L G => a.1 m0 = e.1.1 m0)).card
        * ((Finset.univ.filter
              (fun b : CWQ6ExactCoupledAddress N L G => b.1 m1 = e.2.1.1 m1)).card
          * (Finset.univ.filter
              (fun c : CWQ6ExactCoupledAddress N L G => c.1 m2 = e.2.2.1 m2)).card) := by
  classical
  have hset :
      (Finset.univ : Finset (CWQ6Type2CyclicEdge N L G)).filter
        (fun f => (f.1.1 m0, f.2.1.1 m1, f.2.2.1 m2)
          = (e.1.1 m0, e.2.1.1 m1, e.2.2.1 m2))
        = (Finset.univ.filter
              (fun a : CWQ6ExactCoupledAddress N L G => a.1 m0 = e.1.1 m0)) ×ˢ
          ((Finset.univ.filter
              (fun b : CWQ6ExactCoupledAddress N L G => b.1 m1 = e.2.1.1 m1)) ×ˢ
           (Finset.univ.filter
              (fun c : CWQ6ExactCoupledAddress N L G => c.1 m2 = e.2.2.1 m2))) := by
    ext f
    constructor
    · intro h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at h
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩, ?_⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2.1⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2.2⟩⟩
    · intro h
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp h
      obtain ⟨h2a, h2b⟩ := Finset.mem_product.mp h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2a h2b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      exact ⟨h1, h2a, h2b⟩
  rw [hset]
  exact (Finset.card_product _ _).trans (by rw [Finset.card_product])
theorem solution (N L G : ℕ) (hLG : L + G = N)
    (e : CWQ6Type2CyclicEdge N L G) (i : Fin 3) :
    ((Finset.univ : Finset (CWQ6Type2CyclicEdge N L G)).filter
      (fun f ↦ cwQ6Type2CyclicModeWord f i = cwQ6Type2CyclicModeWord e i)).card =
      Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
  have h0 : ((Finset.univ : Finset (CWQ6Type2CyclicEdge N L G)).filter
      (fun f => (f.1.1 0, f.2.1.1 2, f.2.2.1 1)
        = (e.1.1 0, e.2.1.1 2, e.2.2.1 1))).card
      = Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
    rw [edge_filter_card N L G 0 2 1 e, fiber0 N L G hLG e.1,
      fiber2 N L G hLG e.2.1, fiber1 N L G hLG e.2.2]
    ring
  have h1 : ((Finset.univ : Finset (CWQ6Type2CyclicEdge N L G)).filter
      (fun f => (f.1.1 1, f.2.1.1 0, f.2.2.1 2)
        = (e.1.1 1, e.2.1.1 0, e.2.2.1 2))).card
      = Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
    rw [edge_filter_card N L G 1 0 2 e, fiber1 N L G hLG e.1,
      fiber0 N L G hLG e.2.1, fiber2 N L G hLG e.2.2]
    ring
  have h2 : ((Finset.univ : Finset (CWQ6Type2CyclicEdge N L G)).filter
      (fun f => (f.1.1 2, f.2.1.1 1, f.2.2.1 0)
        = (e.1.1 2, e.2.1.1 1, e.2.2.1 0))).card
      = Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
    rw [edge_filter_card N L G 2 1 0 e, fiber2 N L G hLG e.1,
      fiber1 N L G hLG e.2.1, fiber0 N L G hLG e.2.2]
    ring
  fin_cases i
  · convert h0 using 2
    exact Finset.filter_congr (fun f _ => Iff.rfl)
  · convert h1 using 2
    exact Finset.filter_congr (fun f _ => Iff.rfl)
  · convert h2 using 2
    exact Finset.filter_congr (fun f _ => Iff.rfl)
