-- Prove2me | solution 1 for Couret.CayleyNecessity.odd_multiple_or_neg_of_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:46:15.797061+00:00
-- url     : https://prove2.me/submissions/076ec504-0cd2-49eb-801d-87c0d5a167bc

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d

/-!
COU-20 — research branch only, spectral necessity work in progress.

This file is deliberately separate from the certified Core/Family/Abelian/
Spectral/Parity modules. It does not claim a new Lean or GitHub Actions
certificate until it has been compiled against the pinned toolchain.

The cyclic lemma below produces an odd *discriminating* exponent. It is
slightly more general than the canonical candidate |Q|/3: its exponent
need not be the least such one. Directed adjacency and loops are untouched.

The generic rational charpoly-to-all-power-traces theorem is NOT assumed as
proved. The final assembly is explicitly conditional on that missing bridge.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Couret.CayleyNecessity

/-- Odd cardinality lets us change any natural multiple to an odd one,
without changing its value: adding the group cardinal annihilates alpha. -/
theorem oddify_nsmul
    {Q : Type*} [AddGroup Q] [Finite Q] (alpha beta : Q)
    (hcard : Odd (Nat.card Q)) (k : ℕ) (hk : k • alpha = beta) :
    ∃ n : ℕ, Odd n ∧ n • alpha = beta := by
  classical
  rcases Nat.even_or_odd k with heven | hodd
  · refine ⟨k + Nat.card Q, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := heven
      obtain ⟨v, hv⟩ := hcard
      refine ⟨u + v, ?_⟩
      omega
    · rw [add_nsmul, card_nsmul_eq_zero', add_zero]
      exact hk
  · exact ⟨k, hodd, hk⟩

/-- In a finite odd-order cyclic additive group, every element or its
negative is reached by an odd natural multiple of a specified generator.
The sign is harmless for the two return tests in the directed triple pair. -/
theorem p2m_local_odd_multiple_or_neg_of_cyclic
    {Q : Type*} [AddCommGroup Q] [Finite Q] (alpha delta : Q)
    (hgen : AddSubgroup.zmultiples alpha = ⊤)
    (hcard : Odd (Nat.card Q)) :
    ∃ n : ℕ, Odd n ∧ (n • alpha = delta ∨ n • alpha = -delta) := by
  classical
  have hmem : delta ∈ AddSubgroup.zmultiples alpha := by
    rw [hgen]
    exact AddSubgroup.mem_top delta
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  rcases le_total 0 k with hpos | hneg
  · let n : ℕ := k.toNat
    have hcast : (n : ℤ) = k := Int.toNat_of_nonneg hpos
    have hnat : n • alpha = delta := by
      have h : (n : ℤ) • alpha = delta := by rw [hcast]; exact hk
      simpa only [natCast_zsmul] using h
    obtain ⟨m, hm, heq⟩ := oddify_nsmul alpha delta hcard n hnat
    exact ⟨m, hm, Or.inl heq⟩
  · let n : ℕ := (-k).toNat
    have hcast : (n : ℤ) = -k := Int.toNat_of_nonneg (neg_nonneg.mpr hneg)
    have hnat : n • alpha = -delta := by
      have h : (n : ℤ) • alpha = -delta := by
        rw [hcast, neg_zsmul, hk]
      simpa only [natCast_zsmul] using h
    obtain ⟨m, hm, heq⟩ := oddify_nsmul alpha (-delta) hcard n hnat
    exact ⟨m, hm, Or.inr heq⟩

end Couret.CayleyNecessity

namespace Couret.CayleyDoublet

open Couret.CayleyNecessity

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]











end Couret.CayleyDoublet



universe p2m_u_0
theorem solution : ∀ {Q : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} Q] [Finite.{p2m_u_0 + 1} Q] (alpha delta : Q),
  @Eq.{p2m_u_0 + 1} (@AddSubgroup.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst))
      (@AddSubgroup.zmultiples.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst) alpha)
      (@Top.top.{p2m_u_0} (@AddSubgroup.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst))
        (@AddSubgroup.instTop.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst))) →
    @Odd.{0} Nat Nat.instSemiring (Nat.card.{p2m_u_0} Q) →
      @Exists.{1} Nat fun n =>
        And (@Odd.{0} Nat Nat.instSemiring n)
          (Or
            (@Eq.{p2m_u_0 + 1} Q
              (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                (@instHSMul.{0, p2m_u_0} Nat Q
                  (@AddMonoid.toNSMul.{p2m_u_0} Q
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
                n alpha)
              delta)
            (@Eq.{p2m_u_0 + 1} Q
              (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                (@instHSMul.{0, p2m_u_0} Nat Q
                  (@AddMonoid.toNSMul.{p2m_u_0} Q
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
                n alpha)
              (@Neg.neg.{p2m_u_0} Q
                (@NegZeroClass.toNeg.{p2m_u_0} Q
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} Q
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} Q
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} Q
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} Q inst)))))
                delta))) := @_root_.Couret.CayleyNecessity.p2m_local_odd_multiple_or_neg_of_cyclic

