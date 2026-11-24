-- Prove2me | solution 1 for PythHydra.exists_addr_of_reach
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:08.280976+00:00
-- url     : https://prove2.me/submissions/4a86620a-9075-4c24-9963-5e85582ebf03

-- Thm stub generated from Geometry/PythagoreanHydra/BerggrenAddress.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent

/-!
# The address function of the Berggren tree

The second front of the research mission asks whether the first-order theory of the
Berggren tree *with its address function* (word ↦ triple) can encode Diophantine
machines, producing a Matiyasevich-style undecidability phenomenon.

Here we prove the opposite, in the strongest form available: the address function

`addr : List BStep → ℤ × ℤ × ℤ`,  `addr [] = (3,4,5)`,  `addr (s :: w) = bergₛ (addr w)`

is a **computable bijection** from the free monoid on three letters onto the set of
primitive Pythagorean triples with odd first leg (`addr_bijective`), its inverse is
computed by the inverse Berggren moves (`parent_addr_cons`), and membership is decidable
(`decidableReach` in `BerggrenDescent.lean`).  The Berggren tree is therefore *free*: no
two addresses collide, and the word can be read off from the triple by descent.  In
particular the address relation is decidable, so no undecidable Diophantine phenomenon
can be encoded in it.

The key computation is that the coordinates `uu`, `vv` used by the parent map recover the
parent triple exactly:  `uu (bergA a b c) = a`, `vv (bergA a b c) = -b`, and similarly
`(a, b)` for `bergB` and `(-a, b)` for `bergC` — the *sign pattern* of `(uu, vv)` is
precisely the label of the last Berggren move.
-/

open PythHydra

/-! ### Recovering the last move from the sign pattern -/













/-! ### Hypotenuse estimates -/





/-! ### The address function -/

namespace PythHydra

theorem IsPPT.even_b {a b c : ℤ} (h : IsPPT a b c) : Even b := by
  by_contra hb
  rw [Int.not_even_iff_odd] at hb
  obtain ⟨m, hm⟩ := h.odd
  obtain ⟨n, hn⟩ := hb
  have hp := h.pyth
  unfold IsPythag at hp
  have hc2 : c ^ 2 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by subst hm hn; linarith [hp]; 
  rcases Int.even_or_odd c with ⟨p, hp'⟩ | ⟨p, hp'⟩
  · have : (2 * p) ^ 2 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by
      rw [← hc2, hp']; ring
    have h4 : 4 * p ^ 2 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by linarith [this]
    omega
  · have : (2 * p + 1) ^ 2 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by
      rw [← hc2, hp']
    have h4 : 4 * (p ^ 2 + p) + 1 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by linarith [this]
    omega

end PythHydra

namespace PythHydra

theorem IsPPT.odd_c {a b c : ℤ} (h : IsPPT a b c) : Odd c := by
  have hb := h.even_b
  have ha := h.odd
  have hp := h.pyth
  unfold IsPythag at hp
  rcases Int.even_or_odd c with hc | hc
  · exfalso
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    obtain ⟨p, hp'⟩ := hc
    have h4 : 4 * (m ^ 2 + m) + 1 + 4 * n ^ 2 = 4 * p ^ 2 := by
      subst hm hn hp'; linarith [hp]
    omega
  · exact hc

end PythHydra

namespace PythHydra

theorem recover_a (a b c : ℤ) : uu a b c + 2 * vv a b c + 2 * hh a b c = a := by
  simp only [uu, vv, hh]; ring

end PythHydra

namespace PythHydra

theorem recover_b (a b c : ℤ) : 2 * uu a b c + vv a b c + 2 * hh a b c = b := by
  simp only [uu, vv, hh]; ring

end PythHydra

namespace PythHydra

theorem recover_c (a b c : ℤ) : 2 * uu a b c + 2 * vv a b c + 3 * hh a b c = c := by
  simp only [uu, vv, hh]; ring

end PythHydra

namespace PythHydra

theorem uu_bergA (a b c : ℤ) : uu (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 = a := by
  simp only [uu, bergA_fst, bergA_snd_fst, bergA_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem vv_bergA (a b c : ℤ) : vv (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 = -b := by
  simp only [vv, bergA_fst, bergA_snd_fst, bergA_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem hh_bergA (a b c : ℤ) : hh (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 = c := by
  simp only [hh, bergA_fst, bergA_snd_fst, bergA_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem uu_bergB (a b c : ℤ) : uu (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 = a := by
  simp only [uu, bergB_fst, bergB_snd_fst, bergB_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem vv_bergB (a b c : ℤ) : vv (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 = b := by
  simp only [vv, bergB_fst, bergB_snd_fst, bergB_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem hh_bergB (a b c : ℤ) : hh (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 = c := by
  simp only [hh, bergB_fst, bergB_snd_fst, bergB_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem uu_bergC (a b c : ℤ) : uu (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 = -a := by
  simp only [uu, bergC_fst, bergC_snd_fst, bergC_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem vv_bergC (a b c : ℤ) : vv (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 = b := by
  simp only [vv, bergC_fst, bergC_snd_fst, bergC_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem hh_bergC (a b c : ℤ) : hh (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 = c := by
  simp only [hh, bergC_fst, bergC_snd_fst, bergC_snd_snd]; ring

end PythHydra

namespace PythHydra

theorem parent_bergA {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    parent (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 = (a, b, c) := by
  simp only [parent, PythHydra.uu_bergA, PythHydra.vv_bergA, PythHydra.hh_bergA, abs_of_nonneg ha, abs_neg,
    abs_of_nonneg hb]

end PythHydra

namespace PythHydra

theorem parent_bergB {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    parent (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 = (a, b, c) := by
  simp only [parent, PythHydra.uu_bergB, PythHydra.vv_bergB, PythHydra.hh_bergB, abs_of_nonneg ha, abs_of_nonneg hb]

end PythHydra

namespace PythHydra

theorem parent_bergC {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    parent (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 = (a, b, c) := by
  simp only [parent, PythHydra.uu_bergC, PythHydra.vv_bergC, PythHydra.hh_bergC, abs_neg, abs_of_nonneg ha,
    abs_of_nonneg hb]

end PythHydra

namespace PythHydra

theorem IsPPT.five_le {a b c : ℤ} (h : IsPPT a b c) : 5 ≤ c := by
  by_contra hcon
  push_neg at hcon
  have := small_isPPT h (by omega)
  have : c = 5 := congrArg (fun t => t.2.2) this
  omega

end PythHydra

namespace PythHydra

theorem bergA_hyp_gt {a b c : ℤ} (h : IsPPT a b c) : c < (bergA a b c).2.2 := by
  obtain ⟨_, hbc⟩ := h.legs_lt
  simp only [bergA_snd_snd]
  linarith [h.ha]

end PythHydra

namespace PythHydra

theorem bergB_hyp_gt {a b c : ℤ} (h : IsPPT a b c) : c < (bergB a b c).2.2 := by
  simp only [bergB_snd_snd]
  linarith [h.ha, h.hb, h.hc]

end PythHydra

namespace PythHydra

theorem bergC_hyp_gt {a b c : ℤ} (h : IsPPT a b c) : c < (bergC a b c).2.2 := by
  obtain ⟨hac, _⟩ := h.legs_lt
  simp only [bergC_snd_snd]
  linarith [h.hb]

end PythHydra

namespace PythHydra

@[simp] theorem applyStep_A (t : ℤ × ℤ × ℤ) : applyStep .A t = bergA t.1 t.2.1 t.2.2 := rfl

end PythHydra

namespace PythHydra

@[simp] theorem applyStep_B (t : ℤ × ℤ × ℤ) : applyStep .B t = bergB t.1 t.2.1 t.2.2 := rfl

end PythHydra

namespace PythHydra

@[simp] theorem applyStep_C (t : ℤ × ℤ × ℤ) : applyStep .C t = bergC t.1 t.2.1 t.2.2 := rfl

end PythHydra

namespace PythHydra

theorem children_distinct {a b c : ℤ} (h : IsPPT a b c) :
    bergA a b c ≠ bergB a b c ∧ bergA a b c ≠ bergC a b c ∧ bergB a b c ≠ bergC a b c := by
  have ha := h.ha
  have hb := h.hb
  have hodd := h.odd
  rw [Int.odd_iff] at hodd
  refine ⟨?_, ?_, ?_⟩ <;> intro hcon <;>
    simp only [bergA, bergB, bergC, Prod.mk.injEq] at hcon <;> omega

end PythHydra

namespace PythHydra

theorem addr_isPPT (w : List BStep) : IsPPT (addr w).1 (addr w).2.1 (addr w).2.2 := by
  induction w with
  | nil => exact root_isPPT
  | cons s w ih =>
    cases s <;> simp only [addr, applyStep]
    · exact bergA_isPPT ih
    · exact bergB_isPPT ih
    · exact bergC_isPPT ih

end PythHydra

namespace PythHydra

theorem addr_hyp_gt_five (s : BStep) (w : List BStep) : 5 < (addr (s :: w)).2.2 := by
  have h5 := (PythHydra.addr_isPPT w).five_le
  cases s <;> simp only [addr, applyStep]
  · linarith [PythHydra.bergA_hyp_gt (PythHydra.addr_isPPT w)]
  · linarith [PythHydra.bergB_hyp_gt (PythHydra.addr_isPPT w)]
  · linarith [PythHydra.bergC_hyp_gt (PythHydra.addr_isPPT w)]

end PythHydra

namespace PythHydra

theorem parent_addr_cons (s : BStep) (w : List BStep) :
    parent (addr (s :: w)).1 (addr (s :: w)).2.1 (addr (s :: w)).2.2 = addr w := by
  have h := PythHydra.addr_isPPT w
  have ha : (0 : ℤ) ≤ (addr w).1 := le_of_lt h.ha
  have hb : (0 : ℤ) ≤ (addr w).2.1 := le_of_lt h.hb
  cases s <;> simp only [addr, applyStep]
  · rw [PythHydra.parent_bergA ha hb]
  · rw [PythHydra.parent_bergB ha hb]
  · rw [PythHydra.parent_bergC ha hb]

end PythHydra

namespace PythHydra

theorem addr_injective : Function.Injective addr := by
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ h
    cases w₂ with
    | nil => rfl
    | cons s w =>
      exfalso
      have h1 := PythHydra.addr_hyp_gt_five s w
      rw [← h] at h1
      simp only [addr] at h1
      omega
  | cons s w ih =>
    intro w₂ h
    cases w₂ with
    | nil =>
      exfalso
      have h1 := PythHydra.addr_hyp_gt_five s w
      rw [h] at h1
      simp only [addr] at h1
      omega
    | cons t w' =>
      have hp : addr w = addr w' := by
        rw [← PythHydra.parent_addr_cons s w, ← PythHydra.parent_addr_cons t w', h]
      have hww : w = w' := ih hp
      subst hww
      have hppt := PythHydra.addr_isPPT w
      obtain ⟨hAB, hAC, hBC⟩ := PythHydra.children_distinct hppt
      cases s <;> cases t <;>
        simp only [addr, PythHydra.applyStep_A, PythHydra.applyStep_B, PythHydra.applyStep_C] at h ⊢ <;>
        first
          | exact absurd h hAB
          | exact absurd h hAC
          | exact absurd h hBC
          | exact absurd h.symm hAB
          | exact absurd h.symm hAC
          | exact absurd h.symm hBC

end PythHydra

namespace PythHydra

theorem exists_addr_of_reach {t : ℤ × ℤ × ℤ} (h : Reach t) : ∃ w : List BStep, addr w = t := by
  induction h with
  | root => exact ⟨[], rfl⟩
  | stepA _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨BStep.A :: w, by simp only [addr, PythHydra.applyStep_A, hw]⟩
  | stepB _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨BStep.B :: w, by simp only [addr, PythHydra.applyStep_B, hw]⟩
  | stepC _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨BStep.C :: w, by simp only [addr, PythHydra.applyStep_C, hw]⟩

end PythHydra

namespace PythHydra

theorem exists_addr {a b c : ℤ} (h : IsPPT a b c) : ∃ w : List BStep, addr w = (a, b, c) :=
  exists_addr_of_reach ((reach_iff_isPPT a b c).mpr h)

end PythHydra

namespace PythHydra

theorem addr_bijective :
    Function.Injective addr ∧
      ∀ t : ℤ × ℤ × ℤ, (IsPPT t.1 t.2.1 t.2.2 ↔ ∃ w, addr w = t) := by
  refine ⟨PythHydra.addr_injective, fun t => ⟨fun h => ?_, fun ⟨w, hw⟩ => ?_⟩⟩
  · obtain ⟨a, b, c⟩ := t
    exact PythHydra.exists_addr h
  · rw [← hw]
    exact PythHydra.addr_isPPT w

end PythHydra

namespace PythHydra

theorem exists_unique_addr {a b c : ℤ} (h : IsPPT a b c) :
    ∃! w : List BStep, addr w = (a, b, c) := by
  obtain ⟨w, hw⟩ := PythHydra.exists_addr h
  exact ⟨w, hw, fun w' hw' => PythHydra.addr_injective (by rw [hw, hw'])⟩

end PythHydra


theorem solution {t : ℤ × ℤ × ℤ} (h : Reach t) : ∃ w : List BStep, addr w = t := by
  induction h with
  | root => exact ⟨[], rfl⟩
  | stepA _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨BStep.A :: w, by simp only [addr, PythHydra.applyStep_A, hw]⟩
  | stepB _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨BStep.B :: w, by simp only [addr, PythHydra.applyStep_B, hw]⟩
  | stepC _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨BStep.C :: w, by simp only [addr, PythHydra.applyStep_C, hw]⟩

#print axioms solution
