-- Prove2me | solution 1 for Bridges.ResidueLeakage.jacobiSym_two_no_pruning
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:44:08.85962+00:00
-- url     : https://prove2.me/submissions/5dc34812-0dc9-4cd0-af3c-15350b5e3ca6

-- Sol generated from Bridges/AbelianChannelNoPruning.lean
import Mathlib
import Definitions.Def_Bridges_AbelianChannelNoPruning
import Theorems.Thm_Bridges_ResidueLeakage_abelian_channel_no_pruning
/-
# The abelian channel no-pruning theorem

Fifth file of the residue-leakage thread.  This closes conjecture **C3** of
`FUTURE_DIRECTIONS.md` for a fixed conductor: the Dirichlet no-pruning
phenomenon is not about quadratic residues at all.  It holds for *every* finite
family of Dirichlet characters of a fixed modulus — i.e. for every abelian
residue channel of bounded conductor, in any coefficient ring.

Given probes `χ₁,…,χ_K : DirichletCharacter R M` define the *character
fingerprint* `Φ(N) = [χ_i(N)]`.  For a target `N₀` coprime to `M` and any
candidate prime `p ∤ M`, put `q` in the class `N₀ · p⁻¹ (mod M)`: then
`χ_i(pq) = χ_i(p)·χ_i(N₀ p⁻¹) = χ_i(N₀)` for every `i`, and Dirichlet's theorem
supplies infinitely many primes in that class.

The quadratic case (`Bridges.ResidueLeakageDirichletNoPruning`) is the special
case where each `χ_i` is the Jacobi symbol `(a_i | ·)` of conductor `4a_i`; there
`p⁻¹ ≡ p` up to squares, which is why the compensating class was `N₀ · p`.
-/


open Bridges.ResidueLeakage




/-! ## A quadratic instance: the supplementary symbol at `2` -/

private theorem coprime_eight_of_odd {n : ℕ} (hn : Odd n) : Nat.Coprime n 8 := by
  have h2 : Nat.Coprime n 2 := Nat.coprime_two_right.2 hn
  have := h2.pow_right 3
  norm_num at this
  exact this



open Bridges.ResidueLeakage in
theorem solution{N₀ p : ℕ} (hN₀ : Odd N₀) (hp : Odd p) :
    {q : ℕ | q.Prime ∧ jacobiSym 2 (p * q) = jacobiSym 2 N₀}.Infinite := by
  refine (abelian_channel_no_pruning [ZMod.χ₈] (coprime_eight_of_odd hN₀)
    (coprime_eight_of_odd hp)).mono ?_
  rintro q ⟨hq, hf⟩
  have hval : ZMod.χ₈ ((p * q : ℕ) : ZMod 8) = ZMod.χ₈ ((N₀ : ℕ) : ZMod 8) := by
    simpa only [charFingerprint, List.map_cons, List.map_nil, List.cons.injEq,
      and_true] using hf
  have hNne : ZMod.χ₈ ((N₀ : ℕ) : ZMod 8) ≠ 0 := by
    rw [← jacobiSym.at_two hN₀]
    have hcop : Int.gcd 2 (N₀ : ℕ) = 1 := by
      have : Nat.Coprime 2 N₀ := (Nat.coprime_two_right.2 hN₀).symm
      simpa [Int.gcd] using this
    rcases jacobiSym.eq_one_or_neg_one hcop with h | h <;> rw [h] <;> norm_num
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with rfl | h
    · exfalso
      apply hNne
      rw [← hval, ZMod.χ₈_nat_eq_if_mod_eight]
      simp
    · exact h
  refine ⟨hq, ?_⟩
  rw [jacobiSym.at_two (hp.mul hqodd), jacobiSym.at_two hN₀]
  exact_mod_cast hval
