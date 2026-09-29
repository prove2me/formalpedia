-- Prove2me | solution 1 for Bridges.ResidueLeakage.consistentPairs_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:40:34.454512+00:00
-- url     : https://prove2.me/submissions/436581e8-951e-4ffb-af80-b0c4d25edd74

-- Sol generated from Bridges/ResidueLeakageTorsorTriviality.lean
import Mathlib
import Definitions.Def_Bridges_ResidueLeakageCounting
import Definitions.Def_Bridges_ResidueLeakageDirichletNoPruning
import Definitions.Def_Bridges_ResidueLeakagePatternSurjectivity
import Definitions.Def_Bridges_ResidueLeakageTorsorTriviality
import Theorems.Thm_Bridges_ResidueLeakage_consistent_iff_product_constraint
import Theorems.Thm_Bridges_ResidueLeakage_exists_map_eq_of_nodup
import Theorems.Thm_Bridges_ResidueLeakage_qrFingerprint_range_eq
import Theorems.Thm_Bridges_ResidueLeakage_residue_channel_full_coset
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


/-! ## Bookkeeping: symbols of a prime outside the probe set -/

/-- A prime all of whose probe symbols are nonzero is not itself a probe. -/
theorem not_mem_of_jacobi_ne_zero {A : List ℕ} {x : ℕ} (hx : x.Prime)
    (h : ∀ a ∈ A, jacobiSym (a : ℤ) x ≠ 0) : x ∉ A := by
  intro hxA
  haveI : NeZero x := ⟨hx.ne_zero⟩
  refine h x hxA ?_
  rw [jacobiSym.eq_zero_iff_not_coprime]
  simp [hx.one_lt.ne']

/-- The observed fingerprint has `±1` entries as soon as the target is coprime
to the probes. -/
theorem jacobiSym_target_eq_one_or_neg_one {A : List ℕ} {N₀ : ℕ}
    (hNA : ∀ a ∈ A, Nat.Coprime N₀ a) {a : ℕ} (ha : a ∈ A) :
    jacobiSym (a : ℤ) N₀ = 1 ∨ jacobiSym (a : ℤ) N₀ = -1 := by
  refine jacobiSym.eq_one_or_neg_one ?_
  simpa [Int.gcd_natCast_natCast, Nat.Coprime, Nat.gcd_comm] using (hNA a ha)

/-! ## The factorisation fibre -/



/-! ## Trivial monodromy: the anti-diagonal acts simply transitively -/


/-! ## Torsor form of the no-pruning theorem, and the exact size of the fibre -/





open Bridges.ResidueLeakage in
theorem solution{A : List ℕ} (hA : ∀ a ∈ A, a.Prime) (hnd : A.Nodup)
    {N₀ : ℕ} (hN₀ : Odd N₀) (hNA : ∀ a ∈ A, Nat.Coprime N₀ a) :
    consistentPairs A N₀ =
      {uv : List ℤ × List ℤ | uv.1 ∈ signVectors A.length ∧
        uv.2 = signMul (qrFingerprint A N₀) uv.1} := by
  ext ⟨u, v⟩
  constructor
  · rintro ⟨p, q, hp, hq, hpA, hqA, rfl, rfl, hcons⟩
    have hu : qrFingerprint A p ∈ signVectors A.length := by
      have : qrFingerprint A p ∈
          {v : List ℤ | ∃ q : ℕ, q.Prime ∧ q ∉ A ∧ qrFingerprint A q = v} :=
        ⟨p, hp, hpA, rfl⟩
      rwa [qrFingerprint_range_eq hA hnd] at this
    refine ⟨hu, ?_⟩
    have hpne : ∀ a ∈ A, a ≠ p := fun a ha hap => hpA (hap ▸ ha)
    have hrel := (consistent_iff_product_constraint hA hp hq hpne).1 hcons
    rw [show qrFingerprint A N₀ = A.map (fun a : ℕ => jacobiSym (a : ℤ) N₀) from rfl,
      show qrFingerprint A p = A.map (fun a : ℕ => jacobiSym (a : ℤ) p) from rfl,
      signMul_map]
    exact List.map_congr_left hrel
  · rintro ⟨hu, hv⟩
    dsimp only at hu hv
    subst hv
    obtain ⟨hlen, hentries⟩ := hu
    obtain ⟨ε, hε⟩ := exists_map_eq_of_nodup A hnd u hlen
    have hεA : ∀ a ∈ A, ε a = 1 ∨ ε a = -1 := fun a ha =>
      hentries (ε a) (hε ▸ List.mem_map_of_mem ha)
    obtain ⟨p, q, hp, hq, hpf, hcons⟩ :=
      residue_channel_full_coset hA hnd hN₀ hNA hεA
    have hpsym : ∀ a ∈ A, jacobiSym (a : ℤ) p = ε a := fun a ha =>
      List.map_inj_left.1 hpf a ha
    have hpA : p ∉ A := by
      refine not_mem_of_jacobi_ne_zero hp fun a ha => ?_
      rw [hpsym a ha]
      rcases hεA a ha with h | h <;> rw [h] <;> norm_num
    have hpne : ∀ a ∈ A, a ≠ p := fun a ha hap => hpA (hap ▸ ha)
    have hrel := (consistent_iff_product_constraint hA hp hq hpne).1 hcons
    have hqA : q ∉ A := by
      refine not_mem_of_jacobi_ne_zero hq fun a ha => ?_
      rw [hrel a ha]
      rcases jacobiSym_target_eq_one_or_neg_one hNA ha with h | h <;>
        rcases hεA a ha with h' | h' <;>
        rw [h, hpsym a ha, h'] <;> norm_num
    refine ⟨p, q, hp, hq, hpA, hqA, by rw [hpf, hε], ?_, hcons⟩
    rw [show qrFingerprint A q = A.map (fun a : ℕ => jacobiSym (a : ℤ) q) from rfl,
      show qrFingerprint A N₀ = A.map (fun a : ℕ => jacobiSym (a : ℤ) N₀) from rfl,
      ← hε, signMul_map]
    exact List.map_congr_left fun a ha => by rw [hrel a ha, hpsym a ha]
