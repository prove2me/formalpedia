-- Prove2me | Definitions.Def_Novelty_BerggrenTreeZetaCore
-- name    : Novelty_BerggrenTreeZetaCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-14T01:17:29.49057+00:00
-- url     : https://prove2.me/theorems/6d492059-306c-458e-b408-2288a4b7b7de
-- title:
--   Aether Catalog definitions — Novelty_BerggrenTreeZetaCore
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BerggrenTreeZetaCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BerggrenTreeZetaCore.lean by skeleton subtraction
import Mathlib

/-!
# The Berggren tree of primitive Pythagorean triples: seeds, words, and the hypotenuse

This file is the combinatorial backbone for the "zeta function of the Berggren tree"
project.  It sets up the Berggren ternary tree in its *Euclid-seed* coordinates and
proves the two facts that make an analytic theory possible at all:

* the map `w ↦ seed w` from ternary words to Euclid seeds is a **bijection** onto the
  set of admissible seeds `S = {(m,n) : n < m, 0 < n, gcd(m,n) = 1, m + n odd}`
  (`seed_bijective_onto_seeds`, `seedEquiv`);
* the hypotenuse of a node is `c(w) = m² + n²` (`hyp`), so the tree zeta function is a
  Dirichlet series over `S`.

The three Berggren matrices act on the seed by
`L (m,n) = (2m - n, m)`, `M (m,n) = (2m + n, m)`, `R (m,n) = (m + 2n, n)`,
and we check (`berggren_matrix_L/M/R`) that on the triple `(m²-n², 2mn, m²+n²)` these are
exactly the classical Berggren matrices
`A₁ = !![1,-2,2; 2,-1,2; 2,-2,3]`, `A₂ = !![1,2,2; 2,1,2; 2,2,3]`,
`A₃ = !![-1,2,2; -2,1,2; -2,2,3]` (the last one is `B₃` of `Shared.BerggrenTrees.B`).

## Main results

* `seed_isSeed` — every node of the tree is an admissible Euclid seed;
* `isSeed_reachable` — **completeness** (Berggren's theorem): every admissible seed is a
  node of the tree;
* `seed_injective` — **uniqueness**: distinct words give distinct nodes;
* `seedEquiv` — the resulting equivalence `List (Fin 3) ≃ {p // IsSeed p}`;
* `node_isPPT` — every node carries a primitive Pythagorean triple;
* `hyp_le_silver_pow`, `Mspine_hyp` , `Rspine_hyp` — the growth dichotomy: the largest
  hypotenuse at depth `k` grows like the square of the silver ratio `(1+√2)² = 3+2√2`,
  while the `R`-spine grows only quadratically (`2k² + 6k + 5`).
-/

namespace BerggrenZeta

/-! ## Part A. Seeds, moves and the tree -/

/-- Admissible Euclid seeds: `n < m`, `n ≥ 1`, `gcd (m,n) = 1` and `m + n` odd.
These parametrise primitive Pythagorean triples via `(m²-n², 2mn, m²+n²)`. -/
def IsSeed (p : ℕ × ℕ) : Prop :=
  p.2 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ (p.1 + p.2) % 2 = 1

/-- Berggren move `L` in seed coordinates (matrix `A₁`). -/
def mvL (p : ℕ × ℕ) : ℕ × ℕ := (2 * p.1 - p.2, p.1)

/-- Berggren move `M` in seed coordinates (matrix `A₂`), the Pell/silver branch. -/
def mvM (p : ℕ × ℕ) : ℕ × ℕ := (2 * p.1 + p.2, p.1)

/-- Berggren move `R` in seed coordinates (matrix `A₃ = B₃`). -/
def mvR (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + 2 * p.2, p.2)

/-- The three Berggren moves indexed by `Fin 3`. -/
def step (i : Fin 3) (p : ℕ × ℕ) : ℕ × ℕ :=
  match i with
  | 0 => mvL p
  | 1 => mvM p
  | _ => mvR p

/-- The node of the Berggren tree reached by the word `w` (read right to left),
in Euclid-seed coordinates.  The root is the seed `(2,1)` of the triple `(3,4,5)`. -/
def seed : List (Fin 3) → ℕ × ℕ
  | [] => (2, 1)
  | i :: w => step i (seed w)

/-- The hypotenuse `c(w) = m² + n²` of the node `w`. -/
@[simp] theorem seed_cons (i : Fin 3) (w : List (Fin 3)) :
    seed (i :: w) = step i (seed w) := rfl

def hyp (w : List (Fin 3)) : ℕ := (seed w).1 ^ 2 + (seed w).2 ^ 2

/-- The even leg `2mn` of the node `w`. -/
def legEven (w : List (Fin 3)) : ℕ := 2 * (seed w).1 * (seed w).2

/-- The odd leg `m² - n²` of the node `w`. -/
def legOdd (w : List (Fin 3)) : ℕ := (seed w).1 ^ 2 - (seed w).2 ^ 2



/-! ## Part B. The seed condition is preserved by the moves -/

theorem coprime_mvL {m n : ℕ} (h : Nat.Coprime m n) (hnm : n < m) :
    Nat.Coprime (2 * m - n) m := by
  have hd : Nat.gcd (2 * m - n) m ∣ n := by
    have h1 : Nat.gcd (2 * m - n) m ∣ 2 * m - n := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (2 * m - n) m ∣ 2 * m := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
    have := Nat.dvd_sub h2 h1
    rwa [show 2 * m - (2 * m - n) = n by omega] at this
  have hdm : Nat.gcd (2 * m - n) m ∣ m := Nat.gcd_dvd_right _ _
  have : Nat.gcd (2 * m - n) m ∣ Nat.gcd m n := Nat.dvd_gcd hdm hd
  rw [h] at this
  exact Nat.eq_one_of_dvd_one this

theorem coprime_mvM {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.Coprime (2 * m + n) m := by
  have hd : Nat.gcd (2 * m + n) m ∣ n := by
    have h1 : Nat.gcd (2 * m + n) m ∣ 2 * m + n := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (2 * m + n) m ∣ 2 * m := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
    have := Nat.dvd_sub h1 h2
    rwa [show 2 * m + n - 2 * m = n by omega] at this
  have hdm : Nat.gcd (2 * m + n) m ∣ m := Nat.gcd_dvd_right _ _
  have : Nat.gcd (2 * m + n) m ∣ Nat.gcd m n := Nat.dvd_gcd hdm hd
  rw [h] at this
  exact Nat.eq_one_of_dvd_one this

theorem coprime_mvR {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.Coprime (m + 2 * n) n := by
  have hd : Nat.gcd (m + 2 * n) n ∣ m := by
    have h1 : Nat.gcd (m + 2 * n) n ∣ m + 2 * n := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (m + 2 * n) n ∣ 2 * n := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
    have := Nat.dvd_sub h1 h2
    rwa [show m + 2 * n - 2 * n = m by omega] at this
  have hdn : Nat.gcd (m + 2 * n) n ∣ n := Nat.gcd_dvd_right _ _
  have : Nat.gcd (m + 2 * n) n ∣ Nat.gcd m n := Nat.dvd_gcd hd hdn
  rw [h] at this
  exact Nat.eq_one_of_dvd_one this

theorem isSeed_mvL {p : ℕ × ℕ} (hp : IsSeed p) : IsSeed (mvL p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_, coprime_mvL h3 h1, ?_⟩ <;> simp only [mvL] <;> omega

theorem isSeed_mvM {p : ℕ × ℕ} (hp : IsSeed p) : IsSeed (mvM p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_, coprime_mvM h3, ?_⟩ <;> simp only [mvM] <;> omega

theorem isSeed_mvR {p : ℕ × ℕ} (hp : IsSeed p) : IsSeed (mvR p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_, coprime_mvR h3, ?_⟩ <;> simp only [mvR] <;> omega

theorem isSeed_step (i : Fin 3) {p : ℕ × ℕ} (hp : IsSeed p) : IsSeed (step i p) := by
  fin_cases i
  · exact isSeed_mvL hp
  · exact isSeed_mvM hp
  · exact isSeed_mvR hp

/-- **Every node of the Berggren tree is an admissible Euclid seed.** -/
theorem seed_isSeed (w : List (Fin 3)) : IsSeed (seed w) := by
  induction w with
  | nil =>
    have h21 : seed [] = (2, 1) := rfl
    simp only [h21]
    exact ⟨by norm_num, by norm_num, by decide, by norm_num⟩
  | cons i w ih => exact isSeed_step i ih

/-! ## Part C. Completeness: every admissible seed occurs in the tree -/

/-- A seed is *reachable* if it is the node of some word. -/
def Reachable (p : ℕ × ℕ) : Prop := ∃ w : List (Fin 3), seed w = p

theorem reachable_root : Reachable (2, 1) := ⟨[], rfl⟩

theorem Reachable.mvL {p : ℕ × ℕ} (h : Reachable p) : Reachable (mvL p) := by
  obtain ⟨w, rfl⟩ := h; exact ⟨0 :: w, rfl⟩

theorem Reachable.mvM {p : ℕ × ℕ} (h : Reachable p) : Reachable (mvM p) := by
  obtain ⟨w, rfl⟩ := h; exact ⟨1 :: w, rfl⟩

theorem Reachable.mvR {p : ℕ × ℕ} (h : Reachable p) : Reachable (mvR p) := by
  obtain ⟨w, rfl⟩ := h; exact ⟨2 :: w, rfl⟩

/-- **Berggren completeness.**  Every admissible Euclid seed is a node of the tree. -/
theorem isSeed_reachable : ∀ p : ℕ × ℕ, IsSeed p → Reachable p := by
  intro p
  obtain ⟨m, n⟩ := p
  induction m using Nat.strong_induction_on generalizing n with
  | _ m ih =>
    intro hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    simp only at h1 h2 h3 h4
    by_cases hroot : m = 2 * n
    · -- `m = 2n`: coprimality forces the root
      have hn : n = 1 := by
        have : n ∣ Nat.gcd m n := Nat.dvd_gcd ⟨2, by omega⟩ dvd_rfl
        rw [h3] at this; exact Nat.eq_one_of_dvd_one this
      have hm2 : m = 2 := by omega
      subst hn; subst hm2; exact reachable_root
    rcases lt_trichotomy m (2 * n) with hlt | heq | hgt
    · -- parent `(n, 2n - m)` via move `L`
      have hpar : IsSeed (n, 2 * n - m) := by
        refine ⟨show 2 * n - m < n by omega, show 0 < 2 * n - m by omega, ?_,
          show (n + (2 * n - m)) % 2 = 1 by omega⟩
        have hd : Nat.gcd n (2 * n - m) ∣ m := by
          have hA : Nat.gcd n (2 * n - m) ∣ 2 * n :=
            Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
          have hB : Nat.gcd n (2 * n - m) ∣ 2 * n - m := Nat.gcd_dvd_right _ _
          have := Nat.dvd_sub hA hB
          rwa [show 2 * n - (2 * n - m) = m by omega] at this
        have : Nat.gcd n (2 * n - m) ∣ Nat.gcd m n :=
          Nat.dvd_gcd hd (Nat.gcd_dvd_left _ _)
        rw [h3] at this; exact Nat.eq_one_of_dvd_one this
      have := (ih n (by omega) _ hpar).mvL
      have heq2 : mvL (n, 2 * n - m) = (m, n) := by
        simp only [mvL]
        exact Prod.ext (by simp; omega) (by simp)
      rwa [heq2] at this
    · exact absurd heq hroot
    · rcases lt_trichotomy m (3 * n) with hlt3 | heq3 | hgt3
      · -- parent `(n, m - 2n)` via move `M`
        have hpar : IsSeed (n, m - 2 * n) := by
          refine ⟨show m - 2 * n < n by omega, show 0 < m - 2 * n by omega, ?_,
            show (n + (m - 2 * n)) % 2 = 1 by omega⟩
          have hd : Nat.gcd n (m - 2 * n) ∣ m := by
            have hA : Nat.gcd n (m - 2 * n) ∣ 2 * n :=
              Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
            have hB : Nat.gcd n (m - 2 * n) ∣ m - 2 * n := Nat.gcd_dvd_right _ _
            have := dvd_add hA hB
            rwa [show 2 * n + (m - 2 * n) = m by omega] at this
          have : Nat.gcd n (m - 2 * n) ∣ Nat.gcd m n :=
            Nat.dvd_gcd hd (Nat.gcd_dvd_left _ _)
          rw [h3] at this; exact Nat.eq_one_of_dvd_one this
        have := (ih n (by omega) _ hpar).mvM
        have heq2 : mvM (n, m - 2 * n) = (m, n) := by
          simp only [mvM]
          exact Prod.ext (by simp; omega) (by simp)
        rwa [heq2] at this
      · -- `m = 3n` forces `n = 1`, `m = 3`, contradicting the parity condition
        exfalso
        have hn : n = 1 := by
          have : n ∣ Nat.gcd m n := Nat.dvd_gcd ⟨3, by omega⟩ dvd_rfl
          rw [h3] at this; exact Nat.eq_one_of_dvd_one this
        omega
      · -- parent `(m - 2n, n)` via move `R`
        have hpar : IsSeed (m - 2 * n, n) := by
          refine ⟨show n < m - 2 * n by omega, show 0 < n by omega, ?_,
            show (m - 2 * n + n) % 2 = 1 by omega⟩
          have hd : Nat.gcd (m - 2 * n) n ∣ m := by
            have hA : Nat.gcd (m - 2 * n) n ∣ 2 * n :=
              Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
            have hB : Nat.gcd (m - 2 * n) n ∣ m - 2 * n := Nat.gcd_dvd_left _ _
            have := dvd_add hA hB
            rwa [show 2 * n + (m - 2 * n) = m by omega] at this
          have : Nat.gcd (m - 2 * n) n ∣ Nat.gcd m n :=
            Nat.dvd_gcd hd (Nat.gcd_dvd_right _ _)
          rw [h3] at this; exact Nat.eq_one_of_dvd_one this
        have := (ih (m - 2 * n) (by omega) _ hpar).mvR
        have heq2 : mvR (m - 2 * n, n) = (m, n) := by
          simp only [mvR]
          exact Prod.ext (by simp; omega) (by simp)
        rwa [heq2] at this

/-! ## Part D. Uniqueness: the word is determined by the node -/

theorem mvL_window {p : ℕ × ℕ} (hp : IsSeed p) :
    (mvL p).2 < (mvL p).1 ∧ (mvL p).1 < 2 * (mvL p).2 := by
  obtain ⟨h1, h2, _, _⟩ := hp; constructor <;> (simp [mvL]; omega)

theorem mvM_window {p : ℕ × ℕ} (hp : IsSeed p) :
    2 * (mvM p).2 < (mvM p).1 ∧ (mvM p).1 < 3 * (mvM p).2 := by
  obtain ⟨h1, h2, _, _⟩ := hp; constructor <;> (simp [mvM]; omega)

theorem mvR_window {p : ℕ × ℕ} (hp : IsSeed p) :
    3 * (mvR p).2 < (mvR p).1 := by
  obtain ⟨h1, h2, _, _⟩ := hp; simp [mvR]; omega

theorem mvL_inj {p q : ℕ × ℕ} (hp : IsSeed p) (hq : IsSeed q) (h : mvL p = mvL q) : p = q := by
  obtain ⟨h1, h2, _, _⟩ := hp
  obtain ⟨g1, g2, _, _⟩ := hq
  have h' := congrArg Prod.fst h
  have h'' := congrArg Prod.snd h
  simp [mvL] at h' h''
  exact Prod.ext (by omega) (by omega)

theorem mvM_inj {p q : ℕ × ℕ} (h : mvM p = mvM q) : p = q := by
  have h' := congrArg Prod.fst h
  have h'' := congrArg Prod.snd h
  simp [mvM] at h' h''
  exact Prod.ext (by omega) (by omega)

theorem mvR_inj {p q : ℕ × ℕ} (h : mvR p = mvR q) : p = q := by
  have h' := congrArg Prod.fst h
  have h'' := congrArg Prod.snd h
  simp [mvR] at h' h''
  exact Prod.ext (by omega) (by omega)

/-- Nodes at positive depth are never the root: the root is the unique seed with `m = 2n`. -/
theorem step_ne_root (i : Fin 3) {p : ℕ × ℕ} (hp : IsSeed p) : step i p ≠ (2, 1) := by
  intro h
  fin_cases i
  · have hw := mvL_window hp
    rw [show mvL p = ((2 : ℕ), (1 : ℕ)) from h] at hw
    simp only at hw
    omega
  · have hw := mvM_window hp
    rw [show mvM p = ((2 : ℕ), (1 : ℕ)) from h] at hw
    simp only at hw
    omega
  · have hw := mvR_window hp
    rw [show mvR p = ((2 : ℕ), (1 : ℕ)) from h] at hw
    simp only at hw
    omega

theorem step_inj_index {i j : Fin 3} {p q : ℕ × ℕ} (hp : IsSeed p) (hq : IsSeed q)
    (h : step i p = step j q) : i = j := by
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso
       first
       | (have h1 := mvL_window hp; have h2 := mvM_window hq;
          simp only [step] at h; rw [h] at h1; omega)
       | (have h1 := mvL_window hp; have h2 := mvR_window hq;
          simp only [step] at h; rw [h] at h1; omega)
       | (have h1 := mvM_window hp; have h2 := mvL_window hq;
          simp only [step] at h; rw [h] at h1; omega)
       | (have h1 := mvM_window hp; have h2 := mvR_window hq;
          simp only [step] at h; rw [h] at h1; omega)
       | (have h1 := mvR_window hp; have h2 := mvL_window hq;
          simp only [step] at h; rw [h] at h1; omega)
       | (have h1 := mvR_window hp; have h2 := mvM_window hq;
          simp only [step] at h; rw [h] at h1; omega))

/-- **Uniqueness of the Berggren word.**  The map `w ↦ seed w` is injective. -/
theorem seed_injective : Function.Injective seed := by
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ h
    cases w₂ with
    | nil => rfl
    | cons j w =>
      exact absurd h.symm (step_ne_root j (seed_isSeed w))
  | cons i w ih =>
    intro w₂ h
    cases w₂ with
    | nil => exact absurd h (step_ne_root i (seed_isSeed w))
    | cons j w' =>
      have hij : i = j := step_inj_index (seed_isSeed w) (seed_isSeed w') h
      subst hij
      simp only [seed_cons] at h
      have : seed w = seed w' := by
        fin_cases i
        · exact mvL_inj (seed_isSeed w) (seed_isSeed w') h
        · exact mvM_inj h
        · exact mvR_inj h
      rw [ih this]

/-- **The Berggren tree is exactly the set of Euclid seeds.** -/
theorem seed_bijective_onto_seeds :
    Function.Bijective (fun w : List (Fin 3) => (⟨seed w, seed_isSeed w⟩ : {p // IsSeed p})) := by
  constructor
  · intro w₁ w₂ h
    exact seed_injective (congrArg Subtype.val h)
  · rintro ⟨p, hp⟩
    obtain ⟨w, hw⟩ := isSeed_reachable p hp
    exact ⟨w, by simp [hw]⟩

/-- The bijection between Berggren words and Euclid seeds. -/
noncomputable def seedEquiv : List (Fin 3) ≃ {p : ℕ × ℕ // IsSeed p} :=
  Equiv.ofBijective _ seed_bijective_onto_seeds


/-! ## Part E. The Pythagorean triple at a node, and the Berggren matrices -/



/-- The integer triple `(a, b, c)` at the node `w`. -/
def triple (w : List (Fin 3)) : ℤ × ℤ × ℤ :=
  (((seed w).1 : ℤ) ^ 2 - ((seed w).2 : ℤ) ^ 2, 2 * (seed w).1 * (seed w).2,
    ((seed w).1 : ℤ) ^ 2 + ((seed w).2 : ℤ) ^ 2)




end BerggrenZeta


