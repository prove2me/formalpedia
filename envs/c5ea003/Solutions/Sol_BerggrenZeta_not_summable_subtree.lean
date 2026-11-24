-- Prove2me | solution 1 for BerggrenZeta.not_summable_subtree
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:12.610374+00:00
-- url     : https://prove2.me/submissions/79e4728d-284a-4fb4-af01-2eb429981358

-- Thm stub generated from Novelty/BerggrenTreeHyperbolicSubtree.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeHyperbolicSubtree
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# Purely hyperbolic subtrees: the abscissa drops below `1`

The abscissa of convergence of the full Berggren tree zeta is `1`
(`Novelty.BerggrenTreeZetaAbscissa`), not the silver value `σ₀`; the reason is that two of
the three branches grow only polynomially (`Lspine_hyp`, `Rspine_hyp`).  This file isolates
the mechanism by removing the parabolic directions.

Consider the free binary subtree spanned by the two blocks

* `MM`  (`blockList true  = [1,1]`), and
* `MR`  (`blockList false = [1,2]`),

each of which contains the hyperbolic Pell move `M`.  Write `blocks bs` for the Berggren
word obtained by concatenating the blocks of a bit string `bs`.  Then:

* `blocks_injective` — distinct bit strings give distinct nodes, so the subtree really is a
  free binary tree inside the ternary Berggren tree;
* `hyp_blocks_lower` / `hyp_blocks_upper` — `5 (5/2)^d ≤ c(blocks bs) ≤ 5 (3+2√2)^{2d}` for
  a bit string of length `d`: every block is *expanding*, unlike the pure `R` direction;
* `summable_subtree` — the subtree zeta converges for `s > log 2 / log(5/2) ≈ 0.7565`;
* `not_summable_subtree` — and diverges for `0 < s < log 2 / log((3+2√2)²) ≈ 0.1963`;
* `subtree_summable_at_one` — in particular it **converges at `s = 1`**, where the full tree
  zeta diverges.

So the abscissa of the hyperbolic subtree lies in `[0.196, 0.757] ⊂ (0,1)`: the silver-type
prediction "abscissa = log(branching)/log(growth)" is qualitatively correct once the
parabolic generators are removed, and the failure of the silver abscissa for the full tree
is entirely due to them.
-/

open BerggrenZeta

-- open removed: section is not a namespace

/-! ## Part A. The block subtree -/








/-! ## Part B. Every block expands -/







/-! ## Part C. The subtree zeta -/

open Real
namespace BerggrenZeta

@[simp] theorem seed_nil : seed [] = (2, 1) := rfl

end BerggrenZeta

namespace BerggrenZeta

@[simp] theorem seedEquiv_apply (w : List (Fin 3)) : (seedEquiv w : ℕ × ℕ) = seed w := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem coprime_legs_of_seed {m n : ℕ} (h1 : n < m) (h3 : Nat.Coprime m n)
    (h4 : (m + n) % 2 = 1) : Nat.Coprime (m ^ 2 - n ^ 2) (2 * m * n) := by
  obtain ⟨k, hk⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  subst hk
  have hfac : (n + k) ^ 2 - n ^ 2 = k * (k + 2 * n) := by
    have : (n + k) ^ 2 = n ^ 2 + k * (k + 2 * n) := by ring
    omega
  have hodd : ((n + k) ^ 2 - n ^ 2) % 2 = 1 := by
    rw [hfac]
    have hk1 : Odd k := Nat.odd_iff.mpr (by omega)
    have hk2 : Odd (k + 2 * n) := Nat.odd_iff.mpr (by omega)
    exact Nat.odd_iff.mp (hk1.mul hk2)
  by_contra hcon
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
  set m := n + k with hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hpmn : p ∣ m ∨ p ∣ n := by
    have h2mn : p ∣ 2 * (m * n) := by rw [← mul_assoc]; exact hpb
    rcases (Nat.Prime.dvd_mul hp).mp h2mn with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by have := hp.two_le; omega)
    · exact (Nat.Prime.dvd_mul hp).mp h
  have hsqle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (le_of_lt h1) 2
  rcases hpmn with hmm | hn
  · have hm2 : p ∣ m ^ 2 := Dvd.dvd.pow hmm (by norm_num)
    have hn2 : p ∣ n ^ 2 := by
      have hsub := Nat.dvd_sub hm2 hpa
      rwa [show m ^ 2 - (m ^ 2 - n ^ 2) = n ^ 2 by omega] at hsub
    have : p ∣ Nat.gcd m n := Nat.dvd_gcd hmm (hp.dvd_of_dvd_pow hn2)
    rw [h3] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)
  · have hn2 : p ∣ n ^ 2 := Dvd.dvd.pow hn (by norm_num)
    have hm2 : p ∣ m ^ 2 := by
      have := dvd_add hpa hn2
      rwa [show m ^ 2 - n ^ 2 + n ^ 2 = m ^ 2 by omega] at this
    have : p ∣ Nat.gcd m n := Nat.dvd_gcd (hp.dvd_of_dvd_pow hm2) hn
    rw [h3] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)

end BerggrenZeta

namespace BerggrenZeta

theorem node_isPPT (w : List (Fin 3)) :
    legOdd w ^ 2 + legEven w ^ 2 = hyp w ^ 2 ∧ 0 < legOdd w ∧ 0 < legEven w ∧
      Nat.Coprime (legOdd w) (legEven w) := by
  obtain ⟨h1, h2, h3, h4⟩ := seed_isSeed w
  have hsq : (seed w).2 ^ 2 < (seed w).1 ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [legOdd, legEven, hyp]
    zify [le_of_lt hsq]
    ring
  · simp only [legOdd]; omega
  · simp only [legEven]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) h2
  · simpa [legOdd, legEven] using BerggrenZeta.coprime_legs_of_seed h1 h3 h4

end BerggrenZeta

namespace BerggrenZeta

theorem berggren_matrix_L (w : List (Fin 3)) :
    triple (0 :: w) =
      (let (a, b, c) := triple w; (a - 2 * b + 2 * c, 2 * a - b + 2 * c, 2 * a - 2 * b + 3 * c)) := by
  obtain ⟨h1, _, _, _⟩ := seed_isSeed w
  have h : ((2 * (seed w).1 - (seed w).2 : ℕ) : ℤ) = 2 * (seed w).1 - (seed w).2 := by
    have : (seed w).2 ≤ 2 * (seed w).1 := by omega
    push_cast [this]; ring
  simp only [triple, seed_cons, step, mvL, h]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

end BerggrenZeta

namespace BerggrenZeta

theorem berggren_matrix_M (w : List (Fin 3)) :
    triple (1 :: w) =
      (let (a, b, c) := triple w; (a + 2 * b + 2 * c, 2 * a + b + 2 * c, 2 * a + 2 * b + 3 * c)) := by
  simp only [triple, seed_cons, step, mvM]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> push_cast <;> ring

end BerggrenZeta

namespace BerggrenZeta

theorem berggren_matrix_R (w : List (Fin 3)) :
    triple (2 :: w) =
      (let (a, b, c) := triple w;
        (-a + 2 * b + 2 * c, -2 * a + b + 2 * c, -2 * a + 2 * b + 3 * c)) := by
  simp only [triple, seed_cons, step, mvR]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> push_cast <;> ring

end BerggrenZeta

namespace BerggrenZeta

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

end BerggrenZeta

namespace BerggrenZeta

theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  simp only [Real.sqrt_one] at h
  exact h

end BerggrenZeta

namespace BerggrenZeta

theorem silver_quad_M (m n : ℝ) :
    5 * m ^ 2 + 4 * m * n + n ^ 2 ≤ (3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) := by
  have hs := BerggrenZeta.sqrt_two_sq
  have hgt : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have key : (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (5 * m ^ 2 + 4 * m * n + n ^ 2))
      = ((2 * Real.sqrt 2 - 2) * m - 2 * n) ^ 2 := by
    linear_combination (4 * n ^ 2) * hs
  have hnn : 0 ≤ (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (5 * m ^ 2 + 4 * m * n + n ^ 2)) := by
    rw [key]; positivity
  nlinarith [hnn, hgt]

end BerggrenZeta

namespace BerggrenZeta

theorem silver_quad_R (m n : ℝ) :
    m ^ 2 + 4 * m * n + 5 * n ^ 2 ≤ (3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) := by
  have hs := BerggrenZeta.sqrt_two_sq
  have hgt : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have key : (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (m ^ 2 + 4 * m * n + 5 * n ^ 2))
      = (2 * m - (2 * Real.sqrt 2 - 2) * n) ^ 2 := by
    linear_combination (4 * m ^ 2) * hs
  have hnn : 0 ≤ (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (m ^ 2 + 4 * m * n + 5 * n ^ 2)) := by
    rw [key]; positivity
  nlinarith [hnn, hgt]

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_step_le_silver (i : Fin 3) (w : List (Fin 3)) :
    (hyp (i :: w) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ) := by
  obtain ⟨h1, h2, _, _⟩ := seed_isSeed w
  have h1' : ((seed w).2 : ℝ) < ((seed w).1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < ((seed w).2 : ℝ) := by exact_mod_cast h2
  have hs := BerggrenZeta.sqrt_two_sq
  have hsq := BerggrenZeta.one_le_sqrt_two
  set m : ℝ := ((seed w).1 : ℝ)
  set n : ℝ := ((seed w).2 : ℝ)
  fin_cases i
  · -- move `L`: `5m² - 4mn + n² ≤ 5 (m²+n²) ≤ (3+2√2)(m²+n²)`
    have hle : (seed w).2 ≤ 2 * (seed w).1 := by omega
    show ((hyp ((0 : Fin 3) :: w) : ℕ) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ)
    simp only [hyp, seed_cons, step, mvL]
    push_cast [hle]
    nlinarith
  · -- move `M`: the extremal (Pell) move
    simp only [hyp, seed_cons, step, mvM]
    push_cast
    have := BerggrenZeta.silver_quad_M m n
    nlinarith
  · -- move `R`
    simp only [hyp, seed_cons, step, mvR]
    push_cast
    have := BerggrenZeta.silver_quad_R m n
    nlinarith

end BerggrenZeta

namespace BerggrenZeta

@[simp] theorem hyp_nil : hyp [] = 5 := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_le_silver_pow (w : List (Fin 3)) :
    (hyp w : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hpos : (0 : ℝ) < 3 + 2 * Real.sqrt 2 := by positivity
    calc (hyp (i :: w) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ) := BerggrenZeta.hyp_step_le_silver i w
      _ ≤ (3 + 2 * Real.sqrt 2) * (5 * (3 + 2 * Real.sqrt 2) ^ w.length) := by
          exact mul_le_mul_of_nonneg_left ih (le_of_lt hpos)
      _ = 5 * (3 + 2 * Real.sqrt 2) ^ (i :: w).length := by
          simp [List.length_cons, pow_succ]
          ring

end BerggrenZeta

namespace BerggrenZeta

theorem Lspine_seed (k : ℕ) : seed (Lspine k) = (k + 2, k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : Lspine (k + 1) = (0 : Fin 3) :: Lspine k := rfl
    rw [this, seed_cons, ih]
    simp only [step, mvL]
    exact Prod.ext (by simp; omega) (by simp)

end BerggrenZeta

namespace BerggrenZeta

theorem Rspine_seed (k : ℕ) : seed (Rspine k) = (2 * k + 2, 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : Rspine (k + 1) = (2 : Fin 3) :: Rspine k := rfl
    rw [this, seed_cons, ih]
    simp only [step, mvR]
    exact Prod.ext (by simp; omega) (by simp)

end BerggrenZeta

namespace BerggrenZeta

theorem Lspine_hyp (k : ℕ) : hyp (Lspine k) = 2 * k ^ 2 + 6 * k + 5 := by
  simp only [hyp, BerggrenZeta.Lspine_seed]
  ring

end BerggrenZeta

namespace BerggrenZeta

theorem Rspine_hyp (k : ℕ) : hyp (Rspine k) = 4 * k ^ 2 + 8 * k + 5 := by
  simp only [hyp, BerggrenZeta.Rspine_seed]
  ring

end BerggrenZeta

namespace BerggrenZeta

theorem Mspine_seed_succ (k : ℕ) :
    seed (Mspine (k + 1)) = (2 * (seed (Mspine k)).1 + (seed (Mspine k)).2,
      (seed (Mspine k)).1) := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem Mspine_lower_invariant (k : ℕ) :
    2 * (1 + Real.sqrt 2) ^ k ≤ ((seed (Mspine k)).1 : ℝ) ∧
      2 * (1 + Real.sqrt 2) ^ k * (Real.sqrt 2 - 1) ≤ ((seed (Mspine k)).2 : ℝ) := by
  have hs := BerggrenZeta.sqrt_two_sq
  have h1 := BerggrenZeta.one_le_sqrt_two
  have hsle : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  induction k with
  | zero =>
    constructor
    · norm_num [Mspine, seed]
    · norm_num [Mspine, seed]
      linarith
  | succ k ih =>
    obtain ⟨ihm, ihn⟩ := ih
    have hpow : (0 : ℝ) < (1 + Real.sqrt 2) ^ k := by positivity
    rw [BerggrenZeta.Mspine_seed_succ]
    constructor
    · simp only
      push_cast
      have : 2 * (1 + Real.sqrt 2) ^ (k + 1) =
          2 * (2 * (1 + Real.sqrt 2) ^ k) + 2 * (1 + Real.sqrt 2) ^ k * (Real.sqrt 2 - 1) := by
        rw [pow_succ]
        ring
      rw [this]
      linarith
    · simp only
      have : 2 * (1 + Real.sqrt 2) ^ (k + 1) * (Real.sqrt 2 - 1) = 2 * (1 + Real.sqrt 2) ^ k := by
        rw [pow_succ]
        nlinarith
      rw [this]
      exact ihm

end BerggrenZeta

namespace BerggrenZeta

theorem Mspine_silver_growth (k : ℕ) :
    4 * (3 + 2 * Real.sqrt 2) ^ k ≤ (hyp (Mspine k) : ℝ) ∧
      (hyp (Mspine k) : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ k := by
  have hs := BerggrenZeta.sqrt_two_sq
  have h1 := BerggrenZeta.one_le_sqrt_two
  constructor
  · obtain ⟨hm, -⟩ := BerggrenZeta.Mspine_lower_invariant k
    have hsq : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by nlinarith
    have hpow : ((1 + Real.sqrt 2) ^ k) ^ 2 = (3 + 2 * Real.sqrt 2) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul, hsq]
    have hmpos : (0 : ℝ) ≤ 2 * (1 + Real.sqrt 2) ^ k := by positivity
    have hcast : (hyp (Mspine k) : ℝ)
        = ((seed (Mspine k)).1 : ℝ) ^ 2 + ((seed (Mspine k)).2 : ℝ) ^ 2 := by
      simp only [hyp]
      push_cast
      ring
    rw [hcast]
    nlinarith [sq_nonneg ((seed (Mspine k)).2 : ℝ)]
  · have := BerggrenZeta.hyp_le_silver_pow (Mspine k)
    simpa [Mspine, List.length_replicate] using this

end BerggrenZeta

namespace BerggrenZeta

theorem depth_slice_lower {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    (3 : ℝ) ^ k * (5 * (3 + 2 * Real.sqrt 2) ^ k) ^ (-s) ≤
      ∑ v : Fin k → Fin 3, (hyp (List.ofFn v) : ℝ) ^ (-s) := by
  have hterm : ∀ v : Fin k → Fin 3,
      (5 * (3 + 2 * Real.sqrt 2) ^ k) ^ (-s) ≤ (hyp (List.ofFn v) : ℝ) ^ (-s) := by
    intro v
    have hlen : (List.ofFn v).length = k := by simp
    have hle : (hyp (List.ofFn v) : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ k := by
      have := BerggrenZeta.hyp_le_silver_pow (List.ofFn v)
      rwa [hlen] at this
    have hpos : (0 : ℝ) < (hyp (List.ofFn v) : ℝ) := by
      have : 0 < hyp (List.ofFn v) := by
        obtain ⟨h1, h2, -, -⟩ := seed_isSeed (List.ofFn v)
        simp only [hyp]
        positivity
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  have hcard : (Finset.univ : Finset (Fin k → Fin 3)).card = 3 ^ k := by
    simp [Finset.card_univ]
  have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin k → Fin 3))
    (fun v => (hyp (List.ofFn v) : ℝ) ^ (-s)) _ (fun v _ => hterm v)
  rw [hcard, nsmul_eq_mul] at this
  simpa using this

end BerggrenZeta

namespace BerggrenZeta

@[simp] theorem blocks_nil : blocks [] = [] := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem blocks_cons_true (bs : List Bool) :
    blocks (true :: bs) = (1 : Fin 3) :: (1 : Fin 3) :: blocks bs := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem blocks_cons_false (bs : List Bool) :
    blocks (false :: bs) = (1 : Fin 3) :: (2 : Fin 3) :: blocks bs := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem blocks_length (bs : List Bool) : (blocks bs).length = 2 * bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [BerggrenZeta.blocks_cons_true, BerggrenZeta.blocks_cons_false, ih] <;> ring

end BerggrenZeta

namespace BerggrenZeta

theorem blocks_injective : Function.Injective blocks := by
  intro a
  induction a with
  | nil =>
    intro b hb
    cases b with
    | nil => rfl
    | cons c cs => cases c <;> simp [BerggrenZeta.blocks_cons_true, BerggrenZeta.blocks_cons_false] at hb
  | cons x xs ih =>
    intro b hb
    cases b with
    | nil => cases x <;> simp [BerggrenZeta.blocks_cons_true, BerggrenZeta.blocks_cons_false] at hb
    | cons y ys =>
      cases x <;> cases y <;>
        simp only [BerggrenZeta.blocks_cons_true, BerggrenZeta.blocks_cons_false, List.cons.injEq, true_and] at hb
      · rw [ih hb]
      · exact absurd hb.1 (by decide)
      · exact absurd hb.1 (by decide)
      · rw [ih hb]

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_M_lower (w : List (Fin 3)) :
    (5 / 2 : ℝ) * (hyp w : ℝ) ≤ (hyp ((1 : Fin 3) :: w) : ℝ) := by
  obtain ⟨h1, h2, -, -⟩ := seed_isSeed w
  have h1' : ((seed w).2 : ℝ) < ((seed w).1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < ((seed w).2 : ℝ) := by exact_mod_cast h2
  show (5 / 2 : ℝ) * (hyp w : ℝ) ≤ ((hyp ((1 : Fin 3) :: w) : ℕ) : ℝ)
  simp only [hyp, seed_cons, step, mvM]
  push_cast
  nlinarith

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_R_lower (w : List (Fin 3)) :
    (hyp w : ℝ) ≤ (hyp ((2 : Fin 3) :: w) : ℝ) := by
  obtain ⟨h1, h2, -, -⟩ := seed_isSeed w
  have h1' : ((seed w).2 : ℝ) < ((seed w).1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < ((seed w).2 : ℝ) := by exact_mod_cast h2
  show (hyp w : ℝ) ≤ ((hyp ((2 : Fin 3) :: w) : ℕ) : ℝ)
  simp only [hyp, seed_cons, step, mvR]
  push_cast
  nlinarith

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_pos (w : List (Fin 3)) : (0 : ℝ) < (hyp w : ℝ) := by
  obtain ⟨h1, h2, -, -⟩ := seed_isSeed w
  have : 0 < hyp w := by
    have : 0 < (seed w).2 ^ 2 := by positivity
    simp only [hyp]
    omega
  exact_mod_cast this

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_block_lower (b : Bool) (bs : List Bool) :
    (5 / 2 : ℝ) * (hyp (blocks bs) : ℝ) ≤ (hyp (blocks (b :: bs)) : ℝ) := by
  cases b with
  | true =>
    rw [BerggrenZeta.blocks_cons_true]
    have h1 := BerggrenZeta.hyp_M_lower (blocks bs)
    have h2 := BerggrenZeta.hyp_M_lower ((1 : Fin 3) :: blocks bs)
    have hpos := BerggrenZeta.hyp_pos (blocks bs)
    nlinarith
  | false =>
    rw [BerggrenZeta.blocks_cons_false]
    have h1 := BerggrenZeta.hyp_R_lower (blocks bs)
    have h2 := BerggrenZeta.hyp_M_lower ((2 : Fin 3) :: blocks bs)
    nlinarith

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_blocks_lower (bs : List Bool) :
    5 * (5 / 2 : ℝ) ^ bs.length ≤ (hyp (blocks bs) : ℝ) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hstep := BerggrenZeta.hyp_block_lower b bs
    have : 5 * (5 / 2 : ℝ) ^ (b :: bs).length
        = (5 / 2 : ℝ) * (5 * (5 / 2 : ℝ) ^ bs.length) := by
      simp [List.length_cons, pow_succ]
      ring
    rw [this]
    nlinarith

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_blocks_upper (bs : List Bool) :
    (hyp (blocks bs) : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ (2 * bs.length) := by
  have := BerggrenZeta.hyp_le_silver_pow (blocks bs)
  rwa [BerggrenZeta.blocks_length] at this

end BerggrenZeta

namespace BerggrenZeta

theorem subtreeTerm_nonneg (s : ℝ) (p : (d : ℕ) × (Fin d → Bool)) : 0 ≤ subtreeTerm s p :=
  Real.rpow_nonneg (le_of_lt (BerggrenZeta.hyp_pos _)) _

end BerggrenZeta

namespace BerggrenZeta

theorem summable_subtree {s : ℝ} (hs : Real.log 2 / Real.log (5 / 2) < s) :
    Summable (subtreeTerm s) := by
  have hlog : 0 < Real.log (5 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hspos : 0 < s := by
    have : 0 < Real.log 2 / Real.log (5 / 2 : ℝ) :=
      div_pos (Real.log_pos (by norm_num)) hlog
    linarith
  -- the geometric ratio
  set r : ℝ := 2 * (5 / 2 : ℝ) ^ (-s) with hr
  have hr0 : 0 < r := by
    have : (0 : ℝ) < (5 / 2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
    simpa [hr] using by positivity
  have hr1 : r < 1 := by
    have hlt : Real.log 2 < s * Real.log (5 / 2 : ℝ) := by
      rw [div_lt_iff₀ hlog] at hs
      linarith
    have hexp : (5 / 2 : ℝ) ^ (-s) < 2⁻¹ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5/2)]
      have : Real.exp (Real.log (5 / 2 : ℝ) * -s) < Real.exp (-Real.log 2) := by
        apply Real.exp_lt_exp.2
        nlinarith
      calc Real.exp (Real.log (5 / 2 : ℝ) * -s) < Real.exp (-Real.log 2) := this
        _ = 2⁻¹ := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    rw [hr]
    linarith
  rw [summable_sigma_of_nonneg (BerggrenZeta.subtreeTerm_nonneg s)]
  refine ⟨fun d => Summable.of_finite, ?_⟩
  -- bound the fibre sums by a geometric series
  have hbound : ∀ d : ℕ, ∑' y : Fin d → Bool, subtreeTerm s ⟨d, y⟩
      ≤ (5 : ℝ) ^ (-s) * r ^ d := by
    intro d
    have hterm : ∀ y : Fin d → Bool,
        subtreeTerm s ⟨d, y⟩ ≤ (5 : ℝ) ^ (-s) * ((5 / 2 : ℝ) ^ (-s)) ^ d := by
      intro y
      have hlen : (List.ofFn y).length = d := List.length_ofFn
      have hlow : 5 * (5 / 2 : ℝ) ^ d ≤ (hyp (blocks (List.ofFn y)) : ℝ) := by
        have := BerggrenZeta.hyp_blocks_lower (List.ofFn y)
        rwa [hlen] at this
      have hpos5 : (0 : ℝ) < 5 * (5 / 2 : ℝ) ^ d := by positivity
      have := Real.rpow_le_rpow_of_nonpos hpos5 hlow (neg_nonpos.2 hspos.le)
      refine this.trans_eq ?_
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (5/2 : ℝ) d,
        ← Real.rpow_natCast ((5/2 : ℝ) ^ (-s)) d, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num)]
      ring_nf
    calc ∑' y : Fin d → Bool, subtreeTerm s ⟨d, y⟩
        = ∑ y : Fin d → Bool, subtreeTerm s ⟨d, y⟩ := tsum_fintype _
      _ ≤ ∑ _y : Fin d → Bool, (5 : ℝ) ^ (-s) * ((5 / 2 : ℝ) ^ (-s)) ^ d :=
          Finset.sum_le_sum (fun y _ => hterm y)
      _ = (2 ^ d : ℕ) * ((5 : ℝ) ^ (-s) * ((5 / 2 : ℝ) ^ (-s)) ^ d) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ = (5 : ℝ) ^ (-s) * r ^ d := by
          rw [hr, mul_pow]
          push_cast
          ring
  refine Summable.of_nonneg_of_le (fun d => tsum_nonneg (fun y => BerggrenZeta.subtreeTerm_nonneg s _))
    hbound ?_
  exact (summable_geometric_of_lt_one hr0.le hr1).mul_left _

end BerggrenZeta

namespace BerggrenZeta

theorem not_summable_subtree {s : ℝ} (hs0 : 0 < s)
    (hs : s < Real.log 2 / Real.log ((3 + 2 * Real.sqrt 2) ^ 2)) :
    ¬ Summable (subtreeTerm s) := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := BerggrenZeta.one_le_sqrt_two
  set A : ℝ := (3 + 2 * Real.sqrt 2) ^ 2 with hA
  have hA1 : (1 : ℝ) < A := by
    rw [hA]; nlinarith
  have hApos : (0 : ℝ) < A := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  set q : ℝ := 2 * A ^ (-s) with hq
  have hq1 : 1 < q := by
    have hlt : s * Real.log A < Real.log 2 := by
      rw [lt_div_iff₀ hlogA] at hs
      linarith
    have hexp : 2⁻¹ < A ^ (-s) := by
      rw [Real.rpow_def_of_pos hApos]
      have : Real.exp (-Real.log 2) < Real.exp (Real.log A * -s) := by
        apply Real.exp_lt_exp.2
        nlinarith
      calc (2 : ℝ)⁻¹ = Real.exp (-Real.log 2) := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
        _ < Real.exp (Real.log A * -s) := this
    rw [hq]
    linarith
  intro hsum
  -- the fibre sums must tend to zero
  have hfib := ((summable_sigma_of_nonneg (BerggrenZeta.subtreeTerm_nonneg s)).1 hsum).2
  have hzero := hfib.tendsto_atTop_zero
  -- but they are at least `5^{-s} q^d → ∞`
  have hlow : ∀ d : ℕ, (5 : ℝ) ^ (-s) * q ^ d
      ≤ ∑' y : Fin d → Bool, subtreeTerm s ⟨d, y⟩ := by
    intro d
    have hterm : ∀ y : Fin d → Bool,
        (5 : ℝ) ^ (-s) * (A ^ (-s)) ^ d ≤ subtreeTerm s ⟨d, y⟩ := by
      intro y
      have hlen : (List.ofFn y).length = d := List.length_ofFn
      have hup : (hyp (blocks (List.ofFn y)) : ℝ) ≤ 5 * A ^ d := by
        have := BerggrenZeta.hyp_blocks_upper (List.ofFn y)
        rw [hlen] at this
        calc (hyp (blocks (List.ofFn y)) : ℝ)
            ≤ 5 * (3 + 2 * Real.sqrt 2) ^ (2 * d) := this
          _ = 5 * A ^ d := by rw [hA, ← pow_mul, mul_comm 2 d]
      have hpos := BerggrenZeta.hyp_pos (blocks (List.ofFn y))
      have := Real.rpow_le_rpow_of_nonpos hpos hup (neg_nonpos.2 hs0.le)
      refine le_trans (le_of_eq ?_) this
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast A d,
        ← Real.rpow_natCast (A ^ (-s)) d, ← Real.rpow_mul hApos.le,
        ← Real.rpow_mul hApos.le]
      ring_nf
    calc (5 : ℝ) ^ (-s) * q ^ d
        = (2 ^ d : ℕ) * ((5 : ℝ) ^ (-s) * (A ^ (-s)) ^ d) := by
          rw [hq, mul_pow]
          push_cast
          ring
      _ = ∑ _y : Fin d → Bool, (5 : ℝ) ^ (-s) * (A ^ (-s)) ^ d := by
          simp [Finset.sum_const, Finset.card_univ]
      _ ≤ ∑ y : Fin d → Bool, subtreeTerm s ⟨d, y⟩ :=
          Finset.sum_le_sum (fun y _ => hterm y)
      _ = ∑' y : Fin d → Bool, subtreeTerm s ⟨d, y⟩ := (tsum_fintype _).symm
  have hdiv : Filter.Tendsto (fun d : ℕ => (5 : ℝ) ^ (-s) * q ^ d) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (Real.rpow_pos_of_pos (by norm_num) _)
      (tendsto_pow_atTop_atTop_of_one_lt hq1)
  have hbig : Filter.Tendsto (fun d : ℕ => ∑' y : Fin d → Bool, subtreeTerm s ⟨d, y⟩)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hlow hdiv
  exact not_tendsto_nhds_of_tendsto_atTop hbig 0 hzero

end BerggrenZeta

namespace BerggrenZeta

theorem subtree_summable_at_one : Summable (subtreeTerm 1) := by
  refine BerggrenZeta.summable_subtree ?_
  have hlog : 0 < Real.log (5 / 2 : ℝ) := Real.log_pos (by norm_num)
  rw [div_lt_one hlog]
  exact Real.log_lt_log (by norm_num) (by norm_num)

end BerggrenZeta


theorem solution {s : ℝ} (hs0 : 0 < s)
    (hs : s < Real.log 2 / Real.log ((3 + 2 * Real.sqrt 2) ^ 2)) :
    ¬ Summable (subtreeTerm s) := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := BerggrenZeta.one_le_sqrt_two
  set A : ℝ := (3 + 2 * Real.sqrt 2) ^ 2 with hA
  have hA1 : (1 : ℝ) < A := by
    rw [hA]; nlinarith
  have hApos : (0 : ℝ) < A := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  set q : ℝ := 2 * A ^ (-s) with hq
  have hq1 : 1 < q := by
    have hlt : s * Real.log A < Real.log 2 := by
      rw [lt_div_iff₀ hlogA] at hs
      linarith
    have hexp : 2⁻¹ < A ^ (-s) := by
      rw [Real.rpow_def_of_pos hApos]
      have : Real.exp (-Real.log 2) < Real.exp (Real.log A * -s) := by
        apply Real.exp_lt_exp.2
        nlinarith
      calc (2 : ℝ)⁻¹ = Real.exp (-Real.log 2) := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
        _ < Real.exp (Real.log A * -s) := this
    rw [hq]
    linarith
  intro hsum
  -- the fibre sums must tend to zero
  have hfib := ((summable_sigma_of_nonneg (BerggrenZeta.subtreeTerm_nonneg s)).1 hsum).2
  have hzero := hfib.tendsto_atTop_zero
  -- but they are at least `5^{-s} q^d → ∞`
  have hlow : ∀ d : ℕ, (5 : ℝ) ^ (-s) * q ^ d
      ≤ ∑' y : Fin d → Bool, subtreeTerm s ⟨d, y⟩ := by
    intro d
    have hterm : ∀ y : Fin d → Bool,
        (5 : ℝ) ^ (-s) * (A ^ (-s)) ^ d ≤ subtreeTerm s ⟨d, y⟩ := by
      intro y
      have hlen : (List.ofFn y).length = d := List.length_ofFn
      have hup : (hyp (blocks (List.ofFn y)) : ℝ) ≤ 5 * A ^ d := by
        have := BerggrenZeta.hyp_blocks_upper (List.ofFn y)
        rw [hlen] at this
        calc (hyp (blocks (List.ofFn y)) : ℝ)
            ≤ 5 * (3 + 2 * Real.sqrt 2) ^ (2 * d) := this
          _ = 5 * A ^ d := by rw [hA, ← pow_mul, mul_comm 2 d]
      have hpos := BerggrenZeta.hyp_pos (blocks (List.ofFn y))
      have := Real.rpow_le_rpow_of_nonpos hpos hup (neg_nonpos.2 hs0.le)
      refine le_trans (le_of_eq ?_) this
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast A d,
        ← Real.rpow_natCast (A ^ (-s)) d, ← Real.rpow_mul hApos.le,
        ← Real.rpow_mul hApos.le]
      ring_nf
    calc (5 : ℝ) ^ (-s) * q ^ d
        = (2 ^ d : ℕ) * ((5 : ℝ) ^ (-s) * (A ^ (-s)) ^ d) := by
          rw [hq, mul_pow]
          push_cast
          ring
      _ = ∑ _y : Fin d → Bool, (5 : ℝ) ^ (-s) * (A ^ (-s)) ^ d := by
          simp [Finset.sum_const, Finset.card_univ]
      _ ≤ ∑ y : Fin d → Bool, subtreeTerm s ⟨d, y⟩ :=
          Finset.sum_le_sum (fun y _ => hterm y)
      _ = ∑' y : Fin d → Bool, subtreeTerm s ⟨d, y⟩ := (tsum_fintype _).symm
  have hdiv : Filter.Tendsto (fun d : ℕ => (5 : ℝ) ^ (-s) * q ^ d) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (Real.rpow_pos_of_pos (by norm_num) _)
      (tendsto_pow_atTop_atTop_of_one_lt hq1)
  have hbig : Filter.Tendsto (fun d : ℕ => ∑' y : Fin d → Bool, subtreeTerm s ⟨d, y⟩)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hlow hdiv
  exact not_tendsto_nhds_of_tendsto_atTop hbig 0 hzero

#print axioms solution
