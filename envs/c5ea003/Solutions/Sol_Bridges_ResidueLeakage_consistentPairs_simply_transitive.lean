-- Prove2me | solution 1 for Bridges.ResidueLeakage.consistentPairs_simply_transitive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:44:08.24126+00:00
-- url     : https://prove2.me/submissions/36a82931-8463-43de-ba99-ff879006eee2

-- Sol generated from Bridges/ResidueLeakageTorsorTriviality.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageCounting
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Definitions.Def_Bridges_ResidueLeakageTorsorTriviality
import Theorems.Thm_Bridges_ResidueLeakage_consistentPairs_eq
import Theorems.Thm_Bridges_ResidueLeakage_exists_map_eq_of_nodup
/-
# The consistent factor-fingerprint set is a trivial torsor (conjecture C5, closed)

Eighth file of the residue-leakage thread.  The previous files show that the QR
fingerprint prunes nothing (`dirichlet_no_pruning`), that all `2^K` patterns
occur (`qrFingerprint_pattern_surjective`), and that consistency of a pair of
primes with the observation is *exactly* the symmetric relation
`(a|q) = (a|N₀)·(a|p)` (`consistent_iff_product_constraint`).

Conjecture C5 of `FUTURE_DIRECTIONS.md` asked for the structural reformulation:
the "factorisation fibre"

`Φ(N₀) = { (F_A(p), F_A(q)) : p, q prime, F_A(p·q) = F_A(N₀) }`

should be a *trivial torsor* under the anti-diagonal
`Δ⁻ = { (w, w) : w ∈ {±1}^K }`, and this triviality should be equivalent to the
no-pruning statement.  This file proves it:

* `consistentPairs_eq` — the fibre is precisely the graph of the translation
  `u ↦ F_A(N₀) · u`, i.e. a coset of `Δ⁻` in `{±1}^K × {±1}^K`;
* `consistentPairs_simply_transitive` — `Δ⁻` acts *simply transitively* on the
  fibre (existence **and** uniqueness of the connecting sign vector): the fibre
  has trivial monodromy, so it is a trivial `Δ⁻`-torsor;
* `consistentPairs_fst_eq` — the fibre projects **onto** all of `{±1}^K` in the
  first coordinate, which is the no-pruning theorem in torsor form;
* `consistentPairs_ncard` — the fibre has exactly `2^K` elements, i.e. the
  residue channel leaves exactly the full `K` free bits of `F_A(p)`.

Everything is proved for an arbitrary duplicate-free list `A` of probe primes.
-/


open Bridges.ResidueLeakage

/-! ## Pointwise multiplication of sign vectors -/


theorem signMul_map (A : List ℕ) (f g : ℕ → ℤ) :
    signMul (A.map f) (A.map g) = A.map fun a => f a * g a := by
  induction A with
  | nil => rfl
  | cons a t ih =>
      simp only [signMul, List.map_cons, List.zipWith_cons_cons] at *
      rw [ih]

/-- Membership in `signVectors` for a list presented as a map. -/
theorem map_mem_signVectors {A : List ℕ} {f : ℕ → ℤ}
    (hf : ∀ a ∈ A, f a = 1 ∨ f a = -1) : A.map f ∈ signVectors A.length := by
  refine ⟨by simp, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact hf a ha

/-! ## Bookkeeping: symbols of a prime outside the probe set -/



/-! ## The factorisation fibre -/



/-! ## Trivial monodromy: the anti-diagonal acts simply transitively -/


/-! ## Torsor form of the no-pruning theorem, and the exact size of the fibre -/





open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime)
    (hnd : A.Nodup) {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a)
    {x y : List ℤ × List ℤ} (hx : x ∈ consistentPairs A N₀)
    (hy : y ∈ consistentPairs A N₀) :
    ∃! w : List ℤ, w ∈ signVectors A.length ∧
      y.1 = signMul w x.1 ∧ y.2 = signMul w x.2 := by
  rw [consistentPairs_eq hA hnd hN₀ hNA] at hx hy
  obtain ⟨⟨hxlen, hxent⟩, hx2⟩ := hx
  obtain ⟨⟨hylen, hyent⟩, hy2⟩ := hy
  obtain ⟨ε, hε⟩ := exists_map_eq_of_nodup A hnd x.1 hxlen
  obtain ⟨δ, hδ⟩ := exists_map_eq_of_nodup A hnd y.1 hylen
  have hεA : ∀ a ∈ A, ε a = 1 ∨ ε a = -1 := fun a ha =>
    hxent (ε a) (hε ▸ List.mem_map_of_mem ha)
  have hδA : ∀ a ∈ A, δ a = 1 ∨ δ a = -1 := fun a ha =>
    hyent (δ a) (hδ ▸ List.mem_map_of_mem ha)
  have hsq : ∀ a ∈ A, ε a * ε a = 1 := by
    intro a ha; rcases hεA a ha with h | h <;> rw [h] <;> norm_num
  refine ⟨A.map fun a => δ a * ε a, ⟨map_mem_signVectors ?_, ?_, ?_⟩, ?_⟩
  · intro a ha
    rcases hδA a ha with h | h <;> rcases hεA a ha with h' | h' <;>
      rw [h, h'] <;> norm_num
  · rw [← hε, ← hδ]
    simp only [signMul_map]
    exact (List.map_congr_left fun a ha => by
      rw [mul_assoc, hsq a ha, mul_one]).symm
  · rw [hx2, hy2, ← hε, ← hδ,
      show qrFingerprint A N₀ = A.map (fun a : ℕ => jacobiSym (a : ℤ) N₀) from rfl]
    simp only [signMul_map]
    refine List.map_congr_left fun a ha => ?_
    calc jacobiSym (a : ℤ) N₀ * δ a
        = δ a * (ε a * ε a) * jacobiSym (a : ℤ) N₀ := by rw [hsq a ha]; ring
      _ = δ a * ε a * (jacobiSym (a : ℤ) N₀ * ε a) := by ring
  · rintro w ⟨⟨hwlen, -⟩, hw1, -⟩
    obtain ⟨γ, hγ⟩ := exists_map_eq_of_nodup A hnd w hwlen
    rw [← hγ, ← hε, signMul_map] at hw1
    rw [← hδ] at hw1
    have hpt : ∀ a ∈ A, δ a = γ a * ε a := List.map_inj_left.1 hw1
    rw [← hγ]
    refine List.map_congr_left fun a ha => ?_
    rw [hpt a ha, mul_assoc, hsq a ha, mul_one]
