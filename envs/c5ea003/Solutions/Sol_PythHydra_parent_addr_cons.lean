-- Prove2me | solution 1 for PythHydra.parent_addr_cons
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:24:36.123492+00:00
-- url     : https://prove2.me/submissions/62308e1b-ef32-4621-a52d-d7b6a229aa52

-- Sol generated from Geometry/PythagoreanHydra/BerggrenAddress.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent
import Theorems.Thm_PythHydra_addr_isPPT

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

theorem uu_bergA (a b c : ℤ) : uu (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 = a := by
  simp only [uu, bergA_fst, bergA_snd_fst, bergA_snd_snd]; ring

theorem vv_bergA (a b c : ℤ) : vv (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 = -b := by
  simp only [vv, bergA_fst, bergA_snd_fst, bergA_snd_snd]; ring

theorem hh_bergA (a b c : ℤ) : hh (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 = c := by
  simp only [hh, bergA_fst, bergA_snd_fst, bergA_snd_snd]; ring

theorem uu_bergB (a b c : ℤ) : uu (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 = a := by
  simp only [uu, bergB_fst, bergB_snd_fst, bergB_snd_snd]; ring

theorem vv_bergB (a b c : ℤ) : vv (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 = b := by
  simp only [vv, bergB_fst, bergB_snd_fst, bergB_snd_snd]; ring

theorem hh_bergB (a b c : ℤ) : hh (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 = c := by
  simp only [hh, bergB_fst, bergB_snd_fst, bergB_snd_snd]; ring

theorem uu_bergC (a b c : ℤ) : uu (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 = -a := by
  simp only [uu, bergC_fst, bergC_snd_fst, bergC_snd_snd]; ring

theorem vv_bergC (a b c : ℤ) : vv (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 = b := by
  simp only [vv, bergC_fst, bergC_snd_fst, bergC_snd_snd]; ring

theorem hh_bergC (a b c : ℤ) : hh (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 = c := by
  simp only [hh, bergC_fst, bergC_snd_fst, bergC_snd_snd]; ring

/-- The parent map undoes a Berggren `A`-move. -/
theorem parent_bergA {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    parent (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 = (a, b, c) := by
  simp only [parent, uu_bergA, vv_bergA, hh_bergA, abs_of_nonneg ha, abs_neg,
    abs_of_nonneg hb]

/-- The parent map undoes a Berggren `B`-move. -/
theorem parent_bergB {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    parent (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 = (a, b, c) := by
  simp only [parent, uu_bergB, vv_bergB, hh_bergB, abs_of_nonneg ha, abs_of_nonneg hb]

/-- The parent map undoes a Berggren `C`-move. -/
theorem parent_bergC {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    parent (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 = (a, b, c) := by
  simp only [parent, uu_bergC, vv_bergC, hh_bergC, abs_neg, abs_of_nonneg ha,
    abs_of_nonneg hb]

/-! ### Hypotenuse estimates -/





/-! ### The address function -/














example : addr [BStep.B, BStep.B] = (119, 120, 169) := by decide


open PythHydra in
theorem solution(s : BStep) (w : List BStep) :
    parent (addr (s :: w)).1 (addr (s :: w)).2.1 (addr (s :: w)).2.2 = addr w := by
  have h := addr_isPPT w
  have ha : (0 : ℤ) ≤ (addr w).1 := le_of_lt h.ha
  have hb : (0 : ℤ) ≤ (addr w).2.1 := le_of_lt h.hb
  cases s <;> simp only [addr, applyStep]
  · rw [parent_bergA ha hb]
  · rw [parent_bergB ha hb]
  · rw [parent_bergC ha hb]
