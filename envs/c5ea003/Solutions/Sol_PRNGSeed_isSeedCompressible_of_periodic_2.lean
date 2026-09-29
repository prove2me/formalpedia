-- Prove2me | solution 2 for PRNGSeed.isSeedCompressible_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T10:53:25.556647+00:00
-- url     : https://prove2.me/submissions/05c19da0-43ef-4a9c-8ee0-9c5767b546df

/-
# `PRNGSeed.isSeedCompressible_of_periodic`
Target `53fb4727` (Open; re-read live immediately before submitting).

ORDINARY PROOF — full closure screens CLEAN (five bundles read, no `Theorems.` import).
Gift: **SAFE** — and this is the LEAF: proving it voids `3f0acf92`'s gift, freeing that WA-bearing
target above it.

DEFINITIONS (from the retrieved bundles):
    Bits N                  = Fin N → Bool
    toZ2 b                  = if b then 1 else 0        ofZ2 z = decide (z = 1)
    lfsrBits L c init n     = ofZ2 (lfsrRun (toZ2 ∘ c) (toZ2 ∘ init) n)
    IsSeedCompressible N L w = ∃ c init : Fin L → Bool, ∀ i : Fin N, w i = lfsrBits L c init i
    unitTap p               = fun i => if (i:ℕ) = 0 then 1 else 0

THE WITNESS. Take the unit tap and the first period of `w` as the seed:
    c    := fun i => decide ((i:ℕ) = 0)     so that `toZ2 ∘ c = unitTap p`
    init := fun j => if h : (j:ℕ) < N then w ⟨j, h⟩ else false
Then `lfsrRun (unitTap p) init n = init ⟨n % p, _⟩` (that is `3f0acf92`, RE-DERIVED INLINE below),
so the output at `i` is `w ⟨i % p, _⟩`, which `hper` identifies with `w i`.

THE INDEX BOUND, which is where I expected trouble and did not find it. `init` needs `j < N`, and
`p > N` is NOT excluded by any hypothesis. It is still fine: the ONLY `j` ever supplied is `i % p`
for `i : Fin N`, and `Nat.mod_le` gives `i % p ≤ i < N` regardless of `p`. So the `else false` branch
is never taken. That is also why the bundle assumes no `p ≤ N` anywhere, and why `hper` carries the
guard `∀ h : (i:ℕ) % p < N` rather than a global bound — the guard is always dischargeable.

PROBED, NOT GUESSED: `Nat.mod_le (x y : Nat) : x % y ≤ x` — CORE, Init/Data/Nat/Div/Basic:209 (not
Mathlib; searching Mathlib/Data/Nat for it finds nothing). Plus the lemmas listed in the sibling
`lfsrRun_unitTap` file, all read from source.
-/
import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGSeedDetection
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR

set_option autoImplicit false
set_option maxHeartbeats 1000000

open PRNGSeed PRNGCompression

open PRNGSeed PRNGCompression in
/-- **The target, verbatim.** -/
theorem solution {N p : ℕ} (hp : 0 < p) (w : Bits N)
    (hper : ∀ i : Fin N, ∀ h : (i : ℕ) % p < N, w i = w ⟨(i : ℕ) % p, h⟩) :
    IsSeedCompressible N p w := by
  classical
  -- lfsrRun_unitTap, re-derived inline at ZMod 2 (importing Theorems/ would force the reduction path)
  have hunit : ∀ (init : Fin p → ZMod 2) (n : ℕ),
      lfsrRun (unitTap p) init n = init ⟨n % p, Nat.mod_lt _ hp⟩ := by
    intro init n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [lfsrRun.eq_def]
      by_cases h : n < p
      · rw [dif_pos h]
        congr 1
        exact Fin.val_inj.mp (Nat.mod_eq_of_lt h).symm
      · rw [dif_neg h]
        have hge : n ≥ p := Nat.le_of_not_lt h
        have hzero : ∀ b ∈ (Finset.univ : Finset (Fin p)), b ≠ (⟨0, hp⟩ : Fin p) →
            unitTap p b * lfsrRun (unitTap p) init (n - p + (b : ℕ)) = 0 := by
          intro b _ hb
          have hbv : (b : ℕ) ≠ 0 := by
            intro hc
            exact hb (Fin.val_inj.mp (by simpa using hc))
          simp [unitTap, hbv]
        rw [Finset.sum_eq_single_of_mem (⟨0, hp⟩ : Fin p) (Finset.mem_univ _) hzero]
        have hlt : n - p < n := by omega
        have hidx : (n - p) % p = n % p := (Nat.mod_eq_sub_mod hge).symm
        -- `rw [hidx]` is a DEPENDENT rewrite (the Fin proof term's type depends on the value),
        -- failing with "motive is not type correct". `simp` handles the dependency. Probe-confirmed.
        simp [unitTap, ih (n - p) hlt, hidx]
  -- the Bool <-> ZMod 2 round trip
  have hround : ∀ b : Bool, ofZ2 (toZ2 b) = b := by
    intro b; cases b <;> simp [ofZ2, toZ2]
  refine ⟨fun i => decide ((i : ℕ) = 0),
          fun j => if h : (j : ℕ) < N then w ⟨j, h⟩ else false, ?_⟩
  intro i
  have hc : (fun k : Fin p => toZ2 (decide ((k : ℕ) = 0))) = unitTap p := by
    funext k
    simp [toZ2, unitTap]
  show w i = ofZ2 (lfsrRun (fun k : Fin p => toZ2 (decide ((k : ℕ) = 0)))
      (fun k : Fin p => toZ2 (if h : (k : ℕ) < N then w ⟨k, h⟩ else false)) (i : ℕ))
  rw [hc, hunit]
  have hmodlt : (i : ℕ) % p < N := lt_of_le_of_lt (Nat.mod_le _ _) i.isLt
  rw [dif_pos hmodlt, hround]
  exact hper i hmodlt
