-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_reducedResidue_card_le_totient_mul_card_fiber
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:03:21.715675+00:00
-- url     : https://prove2.me/submissions/06f0b358-3ea6-42d9-abde-8037c52bfd97

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Primorial

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





namespace Wikipedia.SzemeredisTheorem

open Finset



@[simp]
theorem mem_reducedResidues {W b : ℕ} :
    b ∈ reducedResidues W ↔ b < W ∧ W.Coprime b := by
  simp [reducedResidues]

/-- Euler's totient is exactly the number of standard reduced residues. -/
@[simp]
theorem card_reducedResidues (W : ℕ) :
    #(reducedResidues W) = W.totient :=
  rfl

/-- A positive modulus has at least one reduced residue. -/
theorem reducedResidues_nonempty {W : ℕ} (hW : 0 < W) :
    (reducedResidues W).Nonempty := by
  rw [← Finset.card_pos, card_reducedResidues, Nat.totient_pos]
  exact hW







/-- Reduction modulo a positive modulus sends every number coprime to the
modulus into the reduced residue system. -/
theorem mod_mem_reducedResidues {W n : ℕ} (hW : 0 < W)
    (hn : n.Coprime W) :
    n % W ∈ reducedResidues W := by
  rw [mem_reducedResidues]
  refine ⟨Nat.mod_lt n hW, ?_⟩
  exact ((ZMod.coprime_mod_iff_coprime n W).2 hn).symm











end Wikipedia.SzemeredisTheorem

end
open Wikipedia.SzemeredisTheorem
open Finset

open Wikipedia.SzemeredisTheorem in
/-- Finite pigeonhole principle for the `W`-trick, in a division-free
form.  If every element of `S` is coprime to `W`, one reduced residue
class contains enough of `S` that multiplying its size by `φ(W)` covers
all of `S`. -/
theorem solution
    {W : ℕ} (hW : 0 < W) (S : Finset ℕ)
    (hcop : ∀ n ∈ S, n.Coprime W) :
    ∃ b ∈ reducedResidues W,
      #S ≤ W.totient * #(residueFiber S W b) := by
  let q := #S / W.totient
  have hmap : ∀ n ∈ S, n % W ∈ reducedResidues W :=
    fun n hn ↦ mod_mem_reducedResidues hW (hcop n hn)
  have hnonempty : (reducedResidues W).Nonempty :=
    reducedResidues_nonempty hW
  have hbase : #(reducedResidues W) * q ≤ #S := by
    rw [card_reducedResidues]
    exact Nat.mul_div_le _ _
  by_cases heq : #(reducedResidues W) * q = #S
  · obtain ⟨b, hb, hfiber⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := S) (t := reducedResidues W) (f := fun n ↦ n % W)
        hmap hnonempty hbase
    refine ⟨b, hb, ?_⟩
    calc
      #S = #(reducedResidues W) * q := heq.symm
      _ ≤ #(reducedResidues W) * #(residueFiber S W b) := by
        apply Nat.mul_le_mul_left
        simpa [residueFiber] using hfiber
      _ = W.totient * #(residueFiber S W b) := by
        rw [card_reducedResidues]
  · have hstrict : #(reducedResidues W) * q < #S :=
      lt_of_le_of_ne hbase heq
    obtain ⟨b, hb, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s := S) (t := reducedResidues W) (f := fun n ↦ n % W)
        hmap hstrict
    refine ⟨b, hb, ?_⟩
    have hceil :
        #S < #(reducedResidues W) * (q + 1) := by
      simpa [q, card_reducedResidues] using
        Nat.lt_mul_div_succ #S (Nat.totient_pos.mpr hW)
    calc
      #S ≤ #(reducedResidues W) * (q + 1) := hceil.le
      _ ≤ #(reducedResidues W) * #(residueFiber S W b) := by
        apply Nat.mul_le_mul_left
        exact Nat.succ_le_iff.mpr (by simpa [residueFiber] using hfiber)
      _ = W.totient * #(residueFiber S W b) := by
        rw [card_reducedResidues]
